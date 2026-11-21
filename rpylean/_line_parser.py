"""
Direct byte-level parser for lean4export NDJSON lines.

The base JSON parser allocates a tree of JsonObject/JsonInt/JsonString/JsonArray
nodes per line, plus a dict and list per nested object/array. For Init.ndjson
that's tens of millions of short-lived allocations dominated by GC. Since each
line follows one of a small set of known schemas, we walk the bytes directly
and build only the final ``Node`` (skipping the intermediate JSON tree).

Lean4export emits keys in alphabetical order within each object, but for
robustness we don't rely on that — every reader scans for its key by name.
"""

from __future__ import print_function

from rpython.rlib.objectmodel import always_inline
from rpython.rlib.rarithmetic import r_uint
from rpython.rlib.rstring import StringBuilder
from rpython.rlib.rutf8 import unichr_as_utf8_append

from rpylean.exceptions import MalformedLine


class LineCursor(object):
    """A stateful byte cursor over a single NDJSON line."""

    _attrs_ = ['line', 'pos', 'length']

    def __init__(self, line, start=0, end=-1):
        assert start >= 0
        self.line = line
        self.pos = start
        self.length = len(line) if end < 0 else end

    @always_inline
    def reset(self, line, start, end):
        assert start >= 0
        assert end >= 0
        self.line = line
        self.pos = start
        self.length = end

    @always_inline
    def at_eol(self):
        """Return True if at end of line (``self.pos == self.length``, or
        immediately at ``\\n`` / ``\\r\\n`` in chunk-streaming mode, advancing
        past the newline)."""
        p = self.pos
        end = self.length
        if p == end:
            return True
        c = self.line[p]
        if c == '\n':
            self.pos = p + 1
            return True
        if c == '\r' and p + 1 < end and self.line[p + 1] == '\n':
            self.pos = p + 2
            return True
        return False

    @always_inline
    def match_lit(self, lit):
        """Match literal bytes ``lit`` at ``self.pos`` with no whitespace
        skipping. Returns True and advances ``self.pos`` on match."""
        n = len(lit)
        p = self.pos
        if p + n > self.length:
            return False
        line = self.line
        i = 0
        while i < n:
            if line[p + i] != lit[i]:
                return False
            i += 1
        self.pos = p + n
        return True

    @always_inline
    def read_uint_compact(self):
        """Read a non-negative integer at ``self.pos`` with no whitespace
        skipping, or return -1 if no digit is present."""
        line = self.line
        n = self.length
        i = self.pos
        if i >= n:
            return -1
        d = ord(line[i]) - 48
        if r_uint(d) > r_uint(9):
            return -1
        val = d
        i += 1
        while i < n:
            d = ord(line[i]) - 48
            if r_uint(d) > r_uint(9):
                break
            val = val * 10 + d
            i += 1
        self.pos = i
        return val

    def skip_string(self):
        """Advance past a JSON string literal without allocating it."""
        self.skip_ws()
        line = self.line
        n = self.length
        if self.pos >= n or line[self.pos] != '"':
            raise MalformedLine("expected string at pos %d" % self.pos)
        i = self.pos + 1
        while i < n:
            c = line[i]
            if c == '"':
                self.pos = i + 1
                return
            if c == '\\':
                if i + 1 < n and line[i + 1] == 'u':
                    i += 6
                else:
                    i += 2
            else:
                i += 1
        raise MalformedLine("unterminated string at pos %d" % self.pos)

    def read_key_span(self):
        """Read ``"key":`` and return ``(start, end)`` indices in ``self.line``
        (without allocating a substring when unescaped)."""
        self.skip_ws()
        line = self.line
        n = self.length
        if self.pos >= n or line[self.pos] != '"':
            raise MalformedLine("expected string at pos %d" % self.pos)
        i = self.pos + 1
        start = i
        while i < n:
            c = line[i]
            if c == '"':
                end = i
                i += 1
                while i < n:
                    wc = line[i]
                    if wc == ' ' or wc == '\t' or wc == '\r' or wc == '\n':
                        i += 1
                    else:
                        break
                if i >= n or line[i] != ':':
                    raise MalformedLine("expected ':' after key at pos %d" % i)
                self.pos = i + 1
                return start, end
            if c == '\\':
                # Rare escaped key: fall back cleanly via read_key semantics
                raise MalformedLine("escaped key at pos %d" % start)
            i += 1
        raise MalformedLine("unterminated string at pos %d" % start)

    @always_inline
    def span_eq(self, start, end, lit):
        n = len(lit)
        if end - start != n:
            return False
        line = self.line
        i = 0
        while i < n:
            if line[start + i] != lit[i]:
                return False
            i += 1
        return True

    def skip_ws(self):
        line = self.line
        i = self.pos
        n = self.length
        while i < n:
            c = line[i]
            if c == ' ' or c == '\t' or c == '\r' or c == '\n':
                i += 1
            else:
                break
        self.pos = i

    def expect(self, ch):
        self.skip_ws()
        if self.pos >= self.length or self.line[self.pos] != ch:
            raise MalformedLine(
                "expected %s at pos %d in %s" % (ch, self.pos, self.line)
            )
        self.pos += 1

    def maybe(self, ch):
        self.skip_ws()
        if self.pos < self.length and self.line[self.pos] == ch:
            self.pos += 1
            return True
        return False

    def read_int(self):
        self.skip_ws()
        line = self.line
        n = self.length
        i = self.pos
        sign = 1
        if i < n and line[i] == '-':
            sign = -1
            i += 1
        if i >= n or line[i] < '0' or line[i] > '9':
            raise MalformedLine("expected int at pos %d in %s" % (self.pos, line))
        val = 0
        zero = ord('0')
        while i < n:
            c = line[i]
            if c < '0' or c > '9':
                break
            val = val * 10 + ord(c) - zero
            i += 1
        self.pos = i
        return sign * val

    def read_string(self):
        self.skip_ws()
        line = self.line
        n = self.length
        if self.pos >= n or line[self.pos] != '"':
            raise MalformedLine("expected string at pos %d" % self.pos)
        i = self.pos + 1
        start = i
        has_escape = False
        while i < n:
            c = line[i]
            if c == '"':
                self.pos = i + 1
                if not has_escape:
                    return line[start:i]
                return _decode_escapes(line, start, i)
            if c == '\\':
                has_escape = True
                if i + 1 < n and line[i + 1] == 'u':
                    i += 6
                else:
                    i += 2
            else:
                i += 1
        raise MalformedLine("unterminated string at pos %d" % start)

    def read_key(self):
        """Read ``"key":`` and return the key."""
        s = self.read_string()
        self.skip_ws()
        if self.pos >= self.length or self.line[self.pos] != ':':
            raise MalformedLine("expected ':' after key at pos %d" % self.pos)
        self.pos += 1
        return s

    def expect_key(self, expected):
        """Match ``"<expected>":`` literally without allocating the key.

        For known keys this avoids the string slice + dict-style equality
        check the generic ``read_key`` then ``==`` would do — and on hot
        paths (e.g. expecting ``"ie"`` after a disc-first expression body)
        that's millions of avoided allocations per export.
        """
        self.skip_ws()
        line = self.line
        elen = len(expected)
        end = self.pos + elen + 3
        if (
            end > self.length
            or line[self.pos] != '"'
            or line[self.pos + elen + 1] != '"'
            or line[self.pos + elen + 2] != ':'
        ):
            raise MalformedLine(
                "expected key %s at pos %d in %s"
                % (expected, self.pos, self.line)
            )
        j = self.pos + 1
        for k in range(elen):
            if line[j + k] != expected[k]:
                raise MalformedLine(
                    "expected key %s at pos %d in %s"
                    % (expected, self.pos, self.line)
                )
        self.pos = end

    def read_int_array(self):
        self.expect('[')
        result = []
        if self.maybe(']'):
            return result
        while True:
            result.append(self.read_int())
            if self.maybe(']'):
                return result
            self.expect(',')

    def read_bool(self):
        self.skip_ws()
        if self.match_lit("true"):
            return True
        if self.match_lit("false"):
            return False
        raise MalformedLine("expected bool at pos %d" % self.pos)


def _decode_escapes(line, start, end):
    builder = StringBuilder(end - start)
    i = start
    while i < end:
        c = line[i]
        if c == '\\':
            i += 1
            ec = line[i]
            if ec == '"':
                builder.append('"')
            elif ec == '\\':
                builder.append('\\')
            elif ec == '/':
                builder.append('/')
            elif ec == 'b':
                builder.append('\b')
            elif ec == 'f':
                builder.append('\f')
            elif ec == 'n':
                builder.append('\n')
            elif ec == 'r':
                builder.append('\r')
            elif ec == 't':
                builder.append('\t')
            elif ec == 'u':
                code = int(line[i + 1:i + 5], 16)
                unichr_as_utf8_append(builder, code, allow_surrogates=True)
                i += 4
            else:
                raise MalformedLine("bad escape \\%s" % ec)
            i += 1
        else:
            builder.append(c)
            i += 1
    return builder.build()
