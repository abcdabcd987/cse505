# Setup for the Final

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


# Completing the Final

Please complete the problems listed in `ASCIIRegex.v`.


## Building the Final

To build the final, use the Makefile. For example:

```
source configure_coqbin.sh
make
```

Building the final should take seconds.


## Submitting the Final

Package your final by running the `package.sh` script in this directory:

```
./package.sh
```

This will create a file `final.zip` in the parent directory.  Upload this file
to the [505 18au Gradescope](https://www.gradescope.com/courses/26971).  Make
sure to upload to the correct assignment!


## Credits

This final was derived from a project by our friend Bill Harris from Galois
Inc., which in turn was based on material from Software Foundations.
