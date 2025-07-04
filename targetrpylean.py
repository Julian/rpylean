from rpylean.cli import cli


def main(argv):
    return cli.main(argv)


def target(driver, args):
    driver.exe_name = "rpylean-%(backend)s"
    return main
