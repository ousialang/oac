from setuptools import setup, find_packages
from os import path
from io import open
import glob

HERE = path.abspath(path.dirname(__file__))

with open(path.join(HERE, "oac", "__version__.py"), encoding="utf-8") as f:
    version = {}
    exec(f.read(), version)
    VERSION = version["__version__"]

with open(path.join(HERE, "README.md"), encoding="utf-8") as f:
    LONG_DESCRIPTION = f.read()

setup(
    name="oac",
    version=VERSION,
    description="Experimental compiler for the Ousia programming language",
    long_description=LONG_DESCRIPTION,
    long_description_content_type="text/markdown",
    url="https://github.com/neysofu/ousia",
    author="Filippo Costa @neysofu",
    author_email="filippo.costa@protonmail.com",
    packages=find_packages(),
    python_requires=">=3.5",
    install_requires=[
        "click",
        "setuptools>=41",
    ],
    entry_points="""
    [console_scripts]
    oac=oac.cli:cli
    """,
    test_suite="nose.collector",
    tests_require=["nose"],
)