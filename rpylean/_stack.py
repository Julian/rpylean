"""
Room for the machine to recurse.

The machine walks terms recursively, a frame per level of nesting, and
terms nest tens of thousands of levels deep (a Church numeral's normal
form, a long string literal's `List.cons` chain). The main thread's
stack is sized from `RLIMIT_STACK` when the process starts, so getting
a bigger one means raising the limit and starting over.
"""

from rpython.rlib import rgc
from rpython.rlib.rstack import _stack_set_length_fraction
from rpython.rtyper.lltypesystem import lltype, rffi
from rpython.translator.tool.cbuild import ExternalCompilationInfo


#: How much stack to ask for, where the system's hard limit allows it.
WANTED = 1024 * 1024 * 1024

#: What RPython takes a stack budget, and its shadowstack's depth, to
#: be multiples of.
_UNIT = 768 * 1024
_SHADOWSTACK_UNIT = 163840

_eci = ExternalCompilationInfo(
    includes=[
        "sys/resource.h", "unistd.h", "stdlib.h", "limits.h", "stdint.h",
    ],
    post_include_bits=[
        "RPY_EXTERN long rpylean_grow_stack(long wanted, char **argv);",
    ],
    separate_module_sources=["""
#include <sys/resource.h>
#include <unistd.h>
#include <stdlib.h>
#include <limits.h>
#include <stdint.h>
#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif

static int rpylean_executable(char *path, size_t size) {
#ifdef __APPLE__
    uint32_t length = (uint32_t)size;
    return _NSGetExecutablePath(path, &length) == 0;
#else
    ssize_t length = readlink("/proc/self/exe", path, size - 1);
    if (length <= 0)
        return 0;
    path[length] = 0;
    return 1;
#endif
}

/* The stack this process has, in bytes, having first restarted it with
   up to `wanted` if it had less and may have more. */
RPY_EXTERN long rpylean_grow_stack(long wanted, char **argv) {
    struct rlimit limit;
    char path[PATH_MAX];
    rlim_t current, target;
    int have_path;

    if (getrlimit(RLIMIT_STACK, &limit) != 0)
        return 0;
    current = limit.rlim_cur;
    if (current == RLIM_INFINITY || current >= (rlim_t)wanted)
        return wanted;
    if (getenv("RPYLEAN_STACK_GROWN") != NULL)
        return (long)current;

    target = (rlim_t)wanted;
    if (limit.rlim_max != RLIM_INFINITY && limit.rlim_max < target)
        target = limit.rlim_max;
    if (target <= current)
        return (long)current;

    have_path = rpylean_executable(path, sizeof(path));
    if (!have_path && (argv == NULL || argv[0] == NULL || argv[0][0] == 0))
        return (long)current;

    limit.rlim_cur = target;
    if (setrlimit(RLIMIT_STACK, &limit) != 0)
        return (long)current;
    setenv("RPYLEAN_STACK_GROWN", "1", 1);
    if (have_path)
        execv(path, argv);
    if (argv != NULL && argv[0] != NULL && argv[0][0] != 0)
        execvp(argv[0], argv);

    unsetenv("RPYLEAN_STACK_GROWN");
    limit.rlim_cur = current;
    setrlimit(RLIMIT_STACK, &limit);
    return (long)current;
}
"""],
)

_grow_stack = rffi.llexternal(
    "rpylean_grow_stack",
    [rffi.LONG, rffi.CCHARPP],
    rffi.LONG,
    compilation_info=_eci,
)


def grow(argv, fallback):
    """
    Give the machine as much stack as the system allows, restarting
    the process if that is what it takes, and budget for it. With no
    way to tell how much there is, budget ``fallback`` units.
    """
    ll_argv = rffi.liststr2charpp(argv)
    size = _grow_stack(WANTED, ll_argv)
    rffi.free_charpp(ll_argv)
    fraction = fallback
    if size > 0:
        # The rest is left for whatever runs once the budget is spent.
        fraction = (size - size / 8) / float(_UNIT)
    _stack_set_length_fraction(fraction)
    rgc.increase_root_stack_depth(int(fraction * _SHADOWSTACK_UNIT))
