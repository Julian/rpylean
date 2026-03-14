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


def _ansi_wrap(tag, text, ansi_prefixes):
    """
    Wrap text in an ANSI escape sequence.
    """
    if tag not in ansi_prefixes:
        return text
    return ansi_prefixes[tag] + text + _ANSI_RESET


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
    return _ansi_wrap(tag, text, DEFAULT_THEME)


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
