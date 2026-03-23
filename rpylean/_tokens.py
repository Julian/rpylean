from __future__ import print_function

from functools import wraps


def ansi_prefix(default_color, bold):
    """
    Build a 24-bit ANSI colour escape prefix.
    """
    if default_color is None:
        return None
    r = int(default_color[0:2], 16)
    g = int(default_color[2:4], 16)
    b = int(default_color[4:6], 16)
    if bold:
        return "\033[1;38;2;%d;%d;%dm" % (r, g, b)
    return "\033[38;2;%d;%d;%dm" % (r, g, b)


class Token(object):
    """A syntactic category tag for pretty-printed output."""

    _all = []

    def __init__(self, name, default_color=None, bold=False):
        Token._all.append(self)
        self.name = name
        self.ansi_prefix = ansi_prefix(default_color, bold)

    def emit(self, text):
        """Produce a ``(str, str)`` pair for use in a token stream."""
        return (self.name, text)

    def __repr__(self):
        return "Token(%r)" % self.name


KEYWORD = Token("keyword", default_color="569cd6", bold=True)
TRACE = Token("trace", default_color="808080")
DECL_NAME = Token("decl.name", default_color="dcdcaa", bold=True)
BINDER_NAME = Token("binder.name", default_color="c586c0")
SORT = Token("sort", default_color="4ec9b0")
LITERAL = Token("literal", default_color="b5cea8")
LEVEL = Token("level", default_color="9cdcfe")
PUNCT = Token("punctuation", default_color="cccccc")

PLAIN = Token("plain")
ERROR = Token("error", default_color="cc0000")

PROMPT = Token("prompt", default_color="908084")

_ANSI_RESET = "\033[0m"

DEFAULT_THEME = {}
for _token in Token._all:
    _prefix = _token.ansi_prefix
    if _prefix is not None:
        DEFAULT_THEME[_token.name] = _prefix


#: Sentinel indicating no span is present on a ``Diagnostic``.
NO_SPAN = (-1, -1)


class Diagnostic(object):
    """
    A token list paired with an optional span and message for diagnostics.

    ``tokens`` is a plain token list (list of ``(tag, text)`` pairs).
    ``span`` is a ``(start, end)`` pair of token indices into ``tokens``
    delimiting the subexpression to underline, or ``NO_SPAN`` when there is
    no underline.
    ``message`` is the diagnostic message shown below the caret underline.
    """

    def __init__(self, tokens, span, message):
        self.tokens = tokens
        self.span = span
        self.message = message

    def format_with(self, formatter):
        """
        Render this diagnostic into a string using the given formatter.

        When a span is present, a ``^^^^`` caret line is inserted below each
        output line that overlaps the span.  The diagnostic message is
        attached (indented to the caret column) after the last caret line.
        Lines after the last span line are omitted so that content rendered
        after the marked expression does not dangle below the message.
        """
        tokens = self.tokens
        span = self.span
        message = self.message

        if span == NO_SPAN:
            return formatter(tokens) + message

        span_start_idx, span_end_idx = span

        # Render line by line, tracking which lines contain the span.
        lines = []          # completed rendered lines
        current = []        # buffer for the current line
        line_extents = []   # per line: list of (start_col, end_col)

        in_span = False
        span_start_col = 0
        current_extents = []
        col = 0             # plain-text column

        for i, (tag, text) in enumerate(tokens):
            if i == span_start_idx:
                in_span = True
                span_start_col = col

            if i == span_end_idx:
                in_span = False
                current_extents.append((span_start_col, col))

            rendered = formatter([(tag, text)])
            plain_parts = text.split("\n")
            rendered_parts = rendered.split("\n")

            for p, plain_part in enumerate(plain_parts):
                if p > 0:
                    if in_span:
                        current_extents.append((span_start_col, col))
                    lines.append("".join(current))
                    line_extents.append(list(current_extents))
                    current = []
                    current_extents = []
                    col = 0
                    if in_span:
                        span_start_col = 0
                current.append(rendered_parts[p])
                try:
                    col += len(plain_part.decode("utf-8"))
                except (UnicodeDecodeError, AttributeError):
                    col += len(plain_part)

        if in_span:
            current_extents.append((span_start_col, col))
        lines.append("".join(current))
        line_extents.append(list(current_extents))

        # Find the last line with a span extent to attach the message.
        last_span_line = -1
        for j in range(len(lines) - 1, -1, -1):
            if line_extents[j]:
                last_span_line = j
                break

        # Build output, inserting caret lines after spanned lines.
        result_parts = []
        for j, line in enumerate(lines):
            extents = line_extents[j]
            result_parts.append(line)
            if extents:
                leftmost = extents[0][0]
                rightmost = extents[0][1]
                for s, e in extents:
                    if s < leftmost:
                        leftmost = s
                    if e > rightmost:
                        rightmost = e
                caret_width = rightmost - leftmost
                if caret_width < 1:
                    caret_width = 1
                indent_str = " " * leftmost
                result_parts.append("\n")
                result_parts.append(indent_str + "^" * caret_width)
                if j == last_span_line:
                    msg = message
                    if msg.startswith("\n"):
                        msg = msg[1:]
                    for msg_line in msg.split("\n"):
                        result_parts.append("\n")
                        result_parts.append(indent_str + msg_line)
                    break
            if j < len(lines) - 1:
                result_parts.append("\n")

        return "".join(result_parts)


def _ansi_wrap(tag, text):
    """
    Wrap text in an ANSI escape sequence using the default theme.
    """
    if tag not in DEFAULT_THEME:
        return text
    return DEFAULT_THEME[tag] + text + _ANSI_RESET


def formatter(tag_text_to_str):
    @wraps(tag_text_to_str)
    def format(tokens):
        return "".join([tag_text_to_str(tag, text) for tag, text in tokens])

    return format


@formatter
def FORMAT_PLAIN(tag, text):
    return text


@formatter
def FORMAT_COLOR(tag, text):
    return _ansi_wrap(tag, text)


class TokenWriter(object):
    """A stream paired with a formatter, knowing how to write token streams."""

    def __init__(self, stream, formatter):
        self.stream = stream
        self.formatter = formatter

    def write(self, tokens):
        """Render tokens and write to stream."""
        self.stream.write(self.formatter(tokens))

    def writeline(self, tokens):
        """Render tokens and write to stream followed by a newline."""
        self.write(tokens)
        self.stream.write("\n")

    def writeline_diagnostic(self, diagnostic):
        """Render a ``Diagnostic`` and write a newline."""
        self.stream.write(diagnostic.format_with(self.formatter))
        self.stream.write("\n")

    def write_plain(self, string):
        """
        Write a plain string to the stream.
        """
        return self.write([PLAIN.emit(string)])


def indent(tokens, prefix):
    """Return tokens with prefix inserted after every newline in plain tokens."""
    result = []
    for tag, text in tokens:
        if tag == PLAIN.name and "\n" in text:
            parts = text.split("\n")
            for i, part in enumerate(parts):
                if i == 0:
                    result.append(PLAIN.emit(part))
                else:
                    result.append(PLAIN.emit("\n" + prefix + part))
        else:
            result.append((tag, text))
    return result


def writer_from_arg(string, stream):
    """
    Create a token writer from a string provided at the CLI.
    """
    if not string or string == "auto":
        formatter = FORMAT_COLOR if stream.isatty() else FORMAT_PLAIN
    elif string == "yes":
        formatter = FORMAT_COLOR
    elif string == "no":
        formatter = FORMAT_PLAIN
    else:
        from rpylean._rcli import UsageError

        raise UsageError("Unknown color choice: %s" % (string,))
    return TokenWriter(stream, formatter)
