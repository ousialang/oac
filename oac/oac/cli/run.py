import click

from oac.cli import cli

@cli.command()
@click.argument("src", nargs=1, type=click.Path(exists=True))
def run(src):
    """
    Run an Ousia program.
    """
    contents = open(src).read()
    print(contents)