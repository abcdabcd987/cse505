# Setup for Homework 6

To build Coq 8.8 and FRAP, please follow the same setup instructions as for
past homework assignments.


## Linking to FRAP

Once you have built FRAP, you will need to create a symlink in this directory.
For example, if you installed FRAP in your home directory (`~/frap`), then
you should run:

```
ln -s ~/frap frap
```

Note that this will lead to some warning from Coq when building, but
those should be safe to ignore.

# Completing Homework 6

Please complete the problems listed in `HW6.v` (this involves completing
problems in multiple files in this directory).


## Building Homeworks

To build each homework, use the Makefile. For example:

```
source configure_coqbin.sh
make
```

Building a homework should take seconds.


## Submitting Homework Assignments

Package your homework by running the `package.sh` script in this directory:

```
./package.sh
```

This will create a file `hw6.zip` in the parent directory.  Upload this file
to the [505 18au Gradescope](https://www.gradescope.com/courses/26971).  Make
sure to upload to the correct assignment!

