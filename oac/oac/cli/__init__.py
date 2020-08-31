import click

from ..__version__ import __version__

@click.group(name="oac")
@click.version_option(__version__)
def cli():
    """
    Compiler
    """
    pass

from .run import run