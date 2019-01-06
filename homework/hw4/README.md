# Setup for Homework 4

To build Coq 8.8 and FRAP, please follow the same setup instructions as for
past homework assignments.

Technically, this homework does not depend on FRAP, but we have imported it in
`coq/ImpInterpProof.v` so that you can use FRAP tactics if you wish.  You will
still need to create a symlink in this directory to the FRAP book.  For
example, if you installed FRAP in your home directory (`~/frap`), then you
should run:

```
ln -s ~/frap frap
```

The proofs we wrote in the solution use tactics from `coq/StructTactics.v`
which is another tactic library developed here at UW.  We have tried to drop
hints where you may want to use these tactics, but it's still probably a good
idea to skim that file and see what's available.

To build the homework, you first need to configure it.  Ensure your Coq
installation is accessible through your PATH environment variable (this is just
like previous homework assignments), and then *in this directory* run:

```
./configure
```

After this configuration step, running `make proof` should not produce any
errors.


# Building the Interpreter and Running Tests

This homework also features a test harness which compares your semantics
for IMP against those of a Python subset.  Getting the test harness to run
may be a bit tricky, but it can be fun to compare our semantics to the Python
subset and get some confidence we have matched it.

To get the test harness running you will need to have
[opam](https://opam.ocaml.org/) setup and install some dependencies:

```
opam install num menhir
```

Once those are installed (and possibly some additional packages...), running
`make Imp.native` should not produce any errors.

To exercise the test harness, you can run `make test`.  Until you have
finished your homework, most of the tests should fail.  Once the homework
is successfully completed, all the tests should pass.


# Completing Homework 4

Please complete the problems in `coq/ImpInterp.v` and `coq/ImpInterpProof.v`.


## Submitting Homework Assignments

Package your homework by running the `package.sh` script in this directory:

```
make clean
./package.sh
```

This will create a file `hw4.zip` in the parent directory.  Upload this file
to the [505 18au Gradescope](https://www.gradescope.com/courses/26971).  Make
sure to upload to the correct assignment!

