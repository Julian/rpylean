from rpylean import cli


def target(driver, args):
    driver.exe_name = "rpylean-%(backend)s"
    return cli.main
