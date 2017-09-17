# `import` statements
Imports allow to link other packages' code. The basic structure is this:

    import abc.xyz

It is also possible to import single sub-packages, or even more packages at
once:

    import abc

    import abc.xyz.util

You can even use another package under a custom name.  This is especially
useful if some package has a very long name:

    import abc.xyz_long_package_name as xyz

