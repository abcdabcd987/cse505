# Setup for Homework 2

*Setup is real similar to Homework 1*

You will need Coq 8.8 and FRAP.

If you already did this set up Homework 1, then you may only need to symlink to
FRAP in this directory.  You may also need to make sure your `PATH` variables
are configured properly by running the commands under the `Building Homeworks`
heading below.

We have included all the build instructions for convenience in case you are
redoing your setup or working on a new machine.


## Building Coq 8.8

The easiest way to get Coq 8.8 is via [OPAM](https://opam.ocaml.org/doc/Install.html).
If you do not have OPAM, then start by installing OPAM.

Coq has [nice instructions](https://coq.inria.fr/opam/www/using.html) for
installing Coq via OPAM, but they install Coq 8.7, which is out-of-date. For
Coq 8.8 you can do the same thing but with some small changes:

```
export OPAMROOT=~/opam-coq.8.8.0 # installation directory
opam init -n --comp=4.02.3 -j 2 # 2 is the number of CPU cores
opam repo add coq-released http://coq.inria.fr/opam/released
opam install coq.8.8.0 && opam pin add coq 8.8.0
```

This will take some time.


## Building FRAP

You can get FRAP from [here](https://github.com/achlipala/frap). Instructions
are in the package.  You can build the code without building the textbook
itself, but if you would like to build the textbook as well, you need the
`proof.sty` and `tikz-cd.sty` files, which I found in the `texlive-lkproof` and
`texlive-tikz-cd` packages in my package manager, respectively.

Building FRAP will take about half an hour.


## Linking to FRAP

Once you have built FRAP, you will need to create a symlink in this directory.
For example, if you installed FRAP in your home directory (`~/frap`), then
you should run:

```
ln -s ~/frap frap
```


## Completing Homework 2

Please complete the problems in `HW2.v`.


## Building Homeworks

To build each homework, use the Makefile. For example:

```
source configure_coqbin.sh
make
```

Building a homework should take seconds.  The output from building
`HW2Check.v` should indicate if you have remaining admits.


## Submitting Homeworks

Package your homework by running the `package.sh` script in this directory:

```
./package.sh
```

This will create a file `hw1.zip` in the parent directory.  Upload this file
to the [505 18au Gradescope](https://www.gradescope.com/courses/26971).  Make
sure to upload to the correct assignment!
