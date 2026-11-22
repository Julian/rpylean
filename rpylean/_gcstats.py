"""
Translated-only RPython GC memory and timing counters.

Every helper returns 0 / 0.0 when running untranslated on PyPy where
`rgc.get_stats` is unavailable.
"""

from rpython.rlib import rgc
from rpython.rlib.jit import dont_look_inside
from rpython.rlib.objectmodel import specialize, we_are_translated


@dont_look_inside
@specialize.arg(0)
def _get_stat(stat_id):
    # `dont_look_inside` because `gc_get_stats` has no JIT equivalent
    # and `live_memory`/`peak_memory` are reached from traced code via
    # `TypeChecker.tick_wall_time`.
    if we_are_translated():
        return rgc.get_stats(stat_id)
    return 0


def gc_time_seconds():
    """Total GC time so far in seconds."""
    return _get_stat(rgc.TOTAL_GC_TIME) * 0.001


def bytes_allocated():
    """Cumulative bytes allocated so far."""
    return _get_stat(rgc.TOTAL_ALLOCATED_MEMORY)


def live_memory():
    """Current live heap size in bytes."""
    return _get_stat(rgc.TOTAL_MEMORY)


def arena_memory():
    """Live GC-arena bytes (small objects)."""
    return _get_stat(rgc.TOTAL_ARENA_MEMORY)


def rawmalloced_memory():
    """Live raw-malloced bytes (large objects: big lists/dicts/strings)."""
    return _get_stat(rgc.TOTAL_RAWMALLOCED_MEMORY)


def peak_memory():
    """Process-wide peak heap size so far in bytes."""
    return _get_stat(rgc.PEAK_MEMORY)
