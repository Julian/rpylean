"""
A Wadler-style pretty-printing document algebra, ported from Lean's
``Std.Format`` (``Init/Data/Format/Basic.lean``).

A ``Format`` is a tree describing a *set* of possible layouts of some text,
differing in where newlines and indentation are placed.  Given a target
line ``width``, :func:`render` picks the layout that uses the fewest lines
while keeping every line within the width where possible.

The building blocks:

* :data:`NIL` -- the empty document.
* :func:`text` -- a literal string carrying a syntactic-category tag (used
  downstream for syntax-highlighted output).  A string may contain ``"\\n"``,
  which is a *hard* line break: it is always emitted and re-indents to the
  current level.
* :data:`LINE` -- a *soft* line break: rendered as a single space when its
  enclosing group fits on one line, or as a newline (plus indentation) when
  it does not.
* :func:`append` / :func:`concat` -- concatenation.
* :func:`nest` -- increase the indentation level of newlines inside a document.
* :func:`group` -- a flattening group: either all of its soft lines become
  spaces (if the whole group fits) or each is laid out per the group's
  behavior.
* :func:`fill` -- a group that breaks as few soft lines as possible.
* :func:`tag` -- associate a numeric tag with a sub-document; :func:`render`
  reports the token-index range the tagged sub-document occupied (used to
  place diagnostic carets).

The renderer returns a *token list* -- a list of ``(tag, text)`` pairs, the
same representation the rest of rpylean already consumes -- so nothing
downstream needs to change.
"""

from rpylean._tokens import PLAIN, MESSAGE, NO_SPAN

#: ``group`` behaviors, mirroring Lean's ``Format.FlattenBehavior``.
ALL_OR_NONE = 0  # every soft line in the group breaks, or none do
FILL = 1         # break as few soft lines as possible

#: The only tag id we use: marks the sub-document whose output token range
#: should be reported as a diagnostic span.
MARK_TAG = 0

#: Default line width for rendering, used when no terminal width is known.
#: Matches Lean's ``Std.Format.defWidth``.
DEFAULT_WIDTH = 120


class _RenderWidth(object):
    """Holds the process-wide rendering width (a mutable int box)."""

    _attrs_ = ['width']

    def __init__(self):
        self.width = DEFAULT_WIDTH


#: The width :func:`rpylean.objects` renders declarations at. The CLI sets
#: this once at startup from ``--width`` or the detected terminal size.
RENDER_WIDTH = _RenderWidth()


def set_render_width(width):
    """Set the process-wide rendering width."""
    RENDER_WIDTH.width = width


class Format(object):
    _attrs_ = []


class _Nil(Format):
    _attrs_ = []


class _Line(Format):
    _attrs_ = []


class _Text(Format):
    _attrs_ = ['tag', 'string']
    _immutable_fields_ = ['tag', 'string']

    def __init__(self, tag, string):
        self.tag = tag
        self.string = string


class _Append(Format):
    _attrs_ = ['left', 'right']
    _immutable_fields_ = ['left', 'right']

    def __init__(self, left, right):
        self.left = left
        self.right = right


class _Nest(Format):
    _attrs_ = ['indent', 'inner']
    _immutable_fields_ = ['indent', 'inner']

    def __init__(self, indent, inner):
        self.indent = indent
        self.inner = inner


class _Group(Format):
    _attrs_ = ['inner', 'behavior']
    _immutable_fields_ = ['inner', 'behavior']

    def __init__(self, inner, behavior):
        self.inner = inner
        self.behavior = behavior


class _Tag(Format):
    _attrs_ = ['tag_id', 'inner']
    _immutable_fields_ = ['tag_id', 'inner']

    def __init__(self, tag_id, inner):
        self.tag_id = tag_id
        self.inner = inner


NIL = _Nil()
LINE = _Line()


def text(token, string):
    """A literal ``string`` tagged with the syntactic-category ``token``."""
    return _Text(token.name, string)


def append(left, right):
    """Concatenate two documents, dropping ``NIL`` operands."""
    if isinstance(left, _Nil):
        return right
    if isinstance(right, _Nil):
        return left
    return _Append(left, right)


def concat(parts):
    """Concatenate a list of documents."""
    result = NIL
    for part in parts:
        result = append(result, part)
    return result


def nest(indent, inner):
    """Render ``inner`` with the indentation level increased by ``indent``."""
    return _Nest(indent, inner)


def group(inner):
    """A flattening group: all soft lines break together, or none do."""
    return _Group(inner, ALL_OR_NONE)


def fill(inner):
    """A group that breaks as few soft lines as possible."""
    return _Group(inner, FILL)


def tag(tag_id, inner):
    """Associate ``tag_id`` with ``inner`` for span reporting."""
    return _Tag(tag_id, inner)


def _utf8_width(s):
    """
    The number of Unicode code points in the UTF-8 byte string ``s``.

    rpylean strings are UTF-8 bytes, so ``len`` over-counts multi-byte
    characters (``∀``, ``→``, ``↦`` ...).  Layout decisions are made in
    display columns, so we count code points by skipping continuation
    bytes (``0b10xxxxxx``).
    """
    n = 0
    for c in s:
        if (ord(c) & 0xC0) != 0x80:
            n += 1
    return n


# -- Fitting measurement -----------------------------------------------------

class _SpaceResult(object):
    """How much horizontal space a prefix of a document needs."""

    _attrs_ = ['found_line', 'found_flat_hard', 'space']

    def __init__(self, found_line=False, found_flat_hard=False, space=0):
        #: A (soft or hard) line break was reached.
        self.found_line = found_line
        #: A hard line break was reached while measuring as flattened.
        self.found_flat_hard = found_flat_hard
        #: Columns consumed before the first line break (or the end).
        self.space = space


def _space_upto_line(f, flatten, w):
    """
    Columns ``f`` consumes up to its first line break, measured as if its
    enclosing group is ``flatten``ed, stopping once ``w`` is exceeded.
    """
    if isinstance(f, _Nil):
        return _SpaceResult()
    if isinstance(f, _Line):
        if flatten:
            return _SpaceResult(space=1)
        return _SpaceResult(found_line=True)
    if isinstance(f, _Text):
        s = f.string
        nl = s.find("\n")
        if nl < 0:
            return _SpaceResult(space=_utf8_width(s))
        return _SpaceResult(
            found_line=True,
            found_flat_hard=flatten,
            space=_utf8_width(s[:nl]),
        )
    if isinstance(f, _Append):
        r1 = _space_upto_line(f.left, flatten, w)
        if r1.space > w or r1.found_line:
            return r1
        r2 = _space_upto_line(f.right, flatten, w - r1.space)
        return _SpaceResult(
            found_line=r2.found_line,
            found_flat_hard=r2.found_flat_hard,
            space=r1.space + r2.space,
        )
    if isinstance(f, _Nest):
        return _space_upto_line(f.inner, flatten, w)
    if isinstance(f, _Group):
        return _space_upto_line(f.inner, True, w)
    if isinstance(f, _Tag):
        return _space_upto_line(f.inner, flatten, w)
    return _SpaceResult()


# -- Work lists (cons cells, matching Lean's purely-functional stacks) --------
#
# Two distinct cons types so RPython can give each list a single element
# type: one of `_WorkItem`, one of `_WorkGroup`.

class _ItemCons(object):
    _attrs_ = ['head', 'tail']
    _immutable_fields_ = ['head', 'tail']

    def __init__(self, head, tail):
        self.head = head   # a _WorkItem
        self.tail = tail   # an _ItemCons, or None


class _GroupCons(object):
    _attrs_ = ['head', 'tail']
    _immutable_fields_ = ['head', 'tail']

    def __init__(self, head, tail):
        self.head = head   # a _WorkGroup
        self.tail = tail   # a _GroupCons, or None


def _icons(head, tail):
    return _ItemCons(head, tail)


def _gcons(head, tail):
    return _GroupCons(head, tail)


# Flatten-allowability states for a work group.
_DISALLOW = -1     # outside any group; never flatten
_ALLOW_FALSE = 0   # in a group, but it does not fit -> do not flatten
_ALLOW_TRUE = 1    # in a group that fits -> flatten


class _WorkItem(object):
    _attrs_ = ['f', 'indent', 'active_tags']

    def __init__(self, f, indent, active_tags):
        self.f = f
        self.indent = indent
        #: Number of open tags to close once this item is fully rendered.
        self.active_tags = active_tags


class _WorkGroup(object):
    _attrs_ = ['fla', 'flb', 'items']

    def __init__(self, fla, flb, items):
        self.fla = fla        # one of the _ALLOW_*/_DISALLOW states
        self.flb = flb        # ALL_OR_NONE or FILL
        self.items = items    # an _ItemCons list of _WorkItem (or None)


def _should_flatten(fla):
    return fla == _ALLOW_TRUE


def _space_upto_line_groups(groups, w):
    """Measure a ``_GroupCons`` list of work groups up to the first line break."""
    space = 0
    g = groups
    while g is not None:
        wg = g.head
        flatten = _should_flatten(wg.fla)
        it = wg.items
        while it is not None:
            r = _space_upto_line(it.head.f, flatten, w)
            if r.space > w or r.found_line:
                return _SpaceResult(
                    found_line=r.found_line,
                    found_flat_hard=r.found_flat_hard,
                    space=space + r.space,
                )
            space += r.space
            w -= r.space
            it = it.tail
        g = g.tail
    return _SpaceResult(space=space)


class _Renderer(object):
    _attrs_ = ['width', 'out', 'column', 'tag_depth', 'span_start', 'span_end']

    def __init__(self, width):
        self.width = width
        self.out = []          # list of (tag, text) tuples
        self.column = 0
        self.tag_depth = 0
        self.span_start = -1
        self.span_end = -1

    # MonadPrettyFormat-style primitives -----------------------------------

    def push_output(self, tag, s):
        self.out.append((tag, s))
        self.column += _utf8_width(s)

    def push_newline(self, indent):
        self.out.append((PLAIN.name, "\n" + " " * indent))
        self.column = indent

    def start_tag(self):
        if self.span_start == -1:
            self.span_start = len(self.out)
        self.tag_depth += 1

    def end_tags(self, count):
        for _ in range(count):
            if self.tag_depth > 0:
                self.tag_depth -= 1
                if self.tag_depth == 0 and self.span_start != -1 \
                        and self.span_end == -1:
                    self.span_end = len(self.out)

    # Group construction with fit measurement ------------------------------

    def push_group(self, flb, items, gs, w):
        """
        Decide whether the group ``items`` (followed by the remaining work
        ``gs``) fits within ``w``, and push it onto ``gs`` accordingly.
        """
        k = self.column
        budget = w - k
        # Measure the group as it would render if allowed to flatten:
        # ALL_OR_NONE measures flattened; FILL measures only to its next line.
        measure_fla = _ALLOW_TRUE if flb == ALL_OR_NONE else _ALLOW_FALSE
        measure_group = _WorkGroup(measure_fla, flb, items)
        r = _space_upto_line_groups(_gcons(measure_group, None), budget)
        if r.space > budget or r.found_line:
            rprime_space = r.space
        else:
            r2 = _space_upto_line_groups(gs, budget - r.space)
            rprime_space = r.space + r2.space
        fits = (not r.found_flat_hard) and rprime_space <= budget
        fla = _ALLOW_TRUE if fits else _ALLOW_FALSE
        return _gcons(_WorkGroup(fla, flb, items), gs)

    # The core layout loop -------------------------------------------------

    def _with_items(self, g, items, rest_groups):
        """Replace ``g``'s items, returning the new group stack."""
        return _gcons(_WorkGroup(g.fla, g.flb, items), rest_groups)

    def be(self, gs):
        while True:
            if gs is None:
                return
            g = gs.head
            rest_groups = gs.tail
            if g.items is None:
                gs = rest_groups
                continue
            i = g.items.head
            rest_items = g.items.tail
            f = i.f

            if isinstance(f, _Nil):
                self.end_tags(i.active_tags)
                gs = self._with_items(g, rest_items, rest_groups)
                continue

            if isinstance(f, _Tag):
                self.start_tag()
                inner = _WorkItem(f.inner, i.indent, i.active_tags + 1)
                gs = self._with_items(
                    g, _icons(inner, rest_items), rest_groups,
                )
                continue

            if isinstance(f, _Append):
                a = _WorkItem(f.left, i.indent, 0)
                b = _WorkItem(f.right, i.indent, i.active_tags)
                gs = self._with_items(
                    g, _icons(a, _icons(b, rest_items)), rest_groups,
                )
                continue

            if isinstance(f, _Nest):
                inner = _WorkItem(f.inner, i.indent + f.indent, i.active_tags)
                gs = self._with_items(
                    g, _icons(inner, rest_items), rest_groups,
                )
                continue

            if isinstance(f, _Text):
                s = f.string
                nl = s.find("\n")
                if nl < 0:
                    self.push_output(f.tag, s)
                    self.end_tags(i.active_tags)
                    gs = self._with_items(g, rest_items, rest_groups)
                    continue
                # A hard line break embedded in text.
                self.push_output(f.tag, s[:nl])
                self.push_newline(i.indent)
                tail_text = _Text(f.tag, s[nl + 1:])
                remainder = _WorkItem(tail_text, i.indent, i.active_tags)
                new_items = _icons(remainder, rest_items)
                if g.fla == _DISALLOW:
                    gs = self._with_items(g, new_items, rest_groups)
                else:
                    gs = self.push_group(
                        g.flb, new_items, rest_groups, self.width,
                    )
                continue

            if isinstance(f, _Line):
                if g.flb == ALL_OR_NONE:
                    if _should_flatten(g.fla):
                        self.push_output(PLAIN.name, " ")
                        self.end_tags(i.active_tags)
                    else:
                        self.push_newline(i.indent)
                        self.end_tags(i.active_tags)
                    gs = self._with_items(g, rest_items, rest_groups)
                    continue
                # FILL
                if _should_flatten(g.fla):
                    trial = self.push_group(
                        FILL, rest_items, rest_groups, self.width - 1,
                    )
                    if _should_flatten(trial.head.fla):
                        self.push_output(PLAIN.name, " ")
                        self.end_tags(i.active_tags)
                        gs = trial
                        continue
                self.push_newline(i.indent)
                self.end_tags(i.active_tags)
                gs = self.push_group(
                    FILL, rest_items, rest_groups, self.width,
                )
                continue

            if isinstance(f, _Group):
                if _should_flatten(g.fla):
                    inner = _WorkItem(f.inner, i.indent, i.active_tags)
                    gs = self._with_items(
                        g, _icons(inner, rest_items), rest_groups,
                    )
                else:
                    inner = _WorkItem(f.inner, i.indent, i.active_tags)
                    tail_gs = self._with_items(g, rest_items, rest_groups)
                    gs = self.push_group(
                        f.behavior, _icons(inner, None), tail_gs, self.width,
                    )
                continue

            # Unreachable: every Format constructor is handled above.
            self.end_tags(i.active_tags)
            gs = self._with_items(g, rest_items, rest_groups)


def render(f, width=DEFAULT_WIDTH):
    """
    Render ``f`` at the given line ``width``.

    Returns ``(tokens, span)`` where ``tokens`` is a list of ``(tag, text)``
    pairs and ``span`` is the ``(start, end)`` token-index range covered by
    the :func:`tag`-ged sub-document (or :data:`NO_SPAN` if none).
    """
    r = _Renderer(width)
    root_item = _WorkItem(f, 0, 0)
    root_group = _WorkGroup(_DISALLOW, ALL_OR_NONE, _icons(root_item, None))
    r.be(_gcons(root_group, None))
    if r.span_start != -1 and r.span_end != -1:
        return r.out, (r.span_start, r.span_end)
    return r.out, NO_SPAN
