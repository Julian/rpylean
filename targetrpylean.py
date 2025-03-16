def debug(msg):
    print "debug:", msg

def entry_point(argv):
    debug("hello world")
    return 0

def target(*args):
    return entry_point
