# Package definition

Each and every `.ousia` file should come as part of a package. Package
definitions allow developers to declare the name of the package that contains
the file. The package definition should be the first statement in every file.

The syntax for package definitions is the following:

    package abc

The suggested package naming method is very similar to Java's; i.e., name the
package as `author.project`. The package name might be prefixed by an Internet
domain extension of your choice to avoid duplicates (especially when the
author's name is short). For example:

    edu.mit.project
