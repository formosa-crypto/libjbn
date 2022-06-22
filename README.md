# libjbn
BigNums library for Jasmin

# Notes

An extended wiki will be created in the future. In the meantime, some notes on how to use this repository are left here.

The following instructions assume that the Jasmin compiler, `jasminc`, from the [main](https://github.com/jasmin-lang/jasmin/tree/main) branch is installed.
We also need [Easycrypt](https://github.com/EasyCrypt/easycrypt/tree/r2022.04), for instance, release `r2022.04`.

## `src`
To compile existing instantiations of generic code:
```
$ cd src/
$ make
```

To compile and have some information about how the compilation went (count of warnings, errors):
```
$ cd src/
$ make -j4 CI=1
```

To compile just one implementation (run `find src/ -name "*.jazz"` to discover in which directories there are `.jazz` files --- `.jazz` files are the "entry" points for compiling), for instance, `sike434`, which uses 7 limbs:
```
$ cd src/sike/sike434/amd64/ref/
$ make clean # if something is left from the previous step, or you would like to compile again
$ make
```

The compilation result is a `.s` file for each `.jazz` file. If you wish to see the compilation commands that are being run, remove the `@` from `src/Makefile.common` from lines 62 to 75.

## `proof`
The functions that are extracted to the equivalent EasyCrypt representation are specified in files named `EcFlags.mk`. As an example, check the following file `src/sike/EcFlags.mk`.

To extract the implementations:
```
$ cd proof/
$ make extract
```

The corresponding `*_s.ec` and `*_ct.ec` should appear in the corresponding directories. For instance, file `src/sike/sike434/amd64/ref/bn_sike434.jazz` corresponds to `proof/sike/sike434/amd64/ref/bn_sike434_s.ec` and `proof/sike/sike434/amd64/ref/bn_sike434_ct.ec`. 

To extract and check if the extracted files are valid (i.e. `easycrypt` and `jasminc` are properly configured / etc):
```
$ cd proof/
$ make
```

To extract a single implementation, for instance `src/sike/sike434/amd64/ref/`:
```
$ cd proof/
$ make ../src/sike/sike434/amd64/ref/
```

Or:

```
$ cd src/sike/sike434/amd64/ref/
$ make extract
```

The correctness proofs, which import these automatically extracted files, are work in progress. 

## `bench`

To run some benchmarks on existing code (after preparing the environment, for instance, by disabling Turbo-Boost):
```
$ cd bench/
$ make run
```

The previous command builds some benchmark binaries (named `bench`) under `bin` and runs them. To compile just one:
```
$ cd bench/
$ make bin/sike/sike503/amd64/ref/bench
```

`bench` produces some `.csv` files, containing the measurements in CPU cycles, in the directory where is called. This is still work in progress, but running `make report` after `make run` `cat`s all `.csv` files under `bench/bin`.

## `tests`

Work in progress.

