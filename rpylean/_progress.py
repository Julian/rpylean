"""
On-demand progress reporting via signal.

`check` is silent by default — for a multi-million-line export it
emits only the final timing. To learn where the kernel is *right now*
(stuck? still parsing? halfway through?), send:

    kill -INFO <pid>    # macOS / BSD
    kill -USR1 <pid>    # Linux

`install()` (called once at startup) installs a flag-setting handler
for the appropriate signal; the streaming checker polls the flag at
declaration boundaries via `poll()` and prints a progress line to
stderr when it fires. This costs essentially nothing on the no-signal
path — one C function call per declaration to test the flag.

A flag-and-poll design (rather than printing directly from the
handler) is mandatory: RPython signal handlers can't safely allocate
or take the GIL, so the actual `stderr.write` has to happen at a
normal call site.
"""
from __future__ import print_function

import sys

from rpython.rlib import rsignal


# macOS / BSD use SIGINFO (the same signal Ctrl-T sends to the
# foreground process); Linux doesn't have SIGINFO, so we fall back to
# SIGUSR1, the standard "user-defined" signal. Both names are
# auto-imported from the host `signal` module by `rsignal.setup()`,
# so this branch resolves to a constant at translation time and the
# other arm is dead-code-eliminated.
if sys.platform == 'darwin':
    SIGNAL = rsignal.SIGINFO
else:
    SIGNAL = rsignal.SIGUSR1


def install():
    """
    Install the progress signal handler.

    Idempotent (`pypysig_setflag` overwrites any prior handler for the
    same signum).
    """
    rsignal.pypysig_setflag(SIGNAL)


def poll():
    """
    Drain pending signals; return True if our progress signal fired.

    `pypysig_poll` returns one signum per call (or -1 when none
    remain); we loop to flush every pending signal so a SIGINFO sent
    mid-decl isn't held over indefinitely on systems where multiple
    pending signals could shadow each other.
    """
    fired = False
    while True:
        sig = rsignal.pypysig_poll()
        if sig == -1:
            return fired
        if sig == SIGNAL:
            fired = True
