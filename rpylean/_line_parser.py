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

from rpython.rlib.rstring import StringBuilder
from rpython.rlib.rutf8 import unichr_as_utf8_append


class LineCursor(object):
    """A stateful byte cursor over a single NDJSON line."""

    def __init__(self, line):
        self.line = line
        self.pos = 0
        self.length = len(line)

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
            raise ValueError(
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
            raise ValueError("expected int at pos %d in %s" % (self.pos, line))
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
            raise ValueError("expected string at pos %d" % self.pos)
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
        raise ValueError("unterminated string at pos %d" % start)

    def read_key(self):
        """Read ``"key":`` and return the key."""
        s = self.read_string()
        self.skip_ws()
        if self.pos >= self.length or self.line[self.pos] != ':':
            raise ValueError("expected ':' after key at pos %d" % self.pos)
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
            raise ValueError(
                "expected key %s at pos %d in %s"
                % (expected, self.pos, self.line)
            )
        j = self.pos + 1
        for k in range(elen):
            if line[j + k] != expected[k]:
                raise ValueError(
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
        line = self.line
        n = self.length
        if self.pos + 4 <= n and line[self.pos:self.pos + 4] == "true":
            self.pos += 4
            return True
        if self.pos + 5 <= n and line[self.pos:self.pos + 5] == "false":
            self.pos += 5
            return False
        raise ValueError("expected bool at pos %d" % self.pos)


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
                raise ValueError("bad escape \\%s" % ec)
            i += 1
        else:
            builder.append(c)
            i += 1
    return builder.build()
