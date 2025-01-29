[![Release](https://github.com/AliaumeL/polyregular-model-checking/actions/workflows/release.yml/badge.svg)](https://github.com/AliaumeL/polyregular-model-checking/actions/workflows/release.yml)
[![haskell and latex CI](https://github.com/AliaumeL/polyregular-model-checking/actions/workflows/haskell.yml/badge.svg)](https://github.com/AliaumeL/polyregular-model-checking/actions/workflows/haskell.yml)

# Polyregular Functions and Model Checking

> Model checking (star-free) polyregular functions written in a Python-like
  syntax by translating them to first order logic.

The repository is divided in two main parts: first the implementation of the
prototype model checker (in Haskell), and the sources of the associated
research paper (in LaTeX). Examples of code written in Python and their
corresponding first-order logic specification are provided in the `examples`
directory.

## Running

The program can be run using the following methods:

```bash
polyreg-exe -i <input_file> -p <pre_condition_file> -q <post_condition_file>
```

A list of examples input files and pre/post condition files can be found in the
`polyreg/assets` subdirectory. The program will output the result of the model
checking process, which can be, for every solver, one of the following:

- `OK`: the program satisfies the specification.
- `KO`: the program does not satisfy the specification.
- `UNKNOWN`: the solver could not determine the result.
- `ERROR`: an error occurred during the model checking process.

The program can also be run in an interactive `web` mode, by running the command
using the `--web` flag. In this mode, the program will start a web server on
the port `3000` and will provide a web interface to run the model checker.

```bash
polyreg-exe --web
```

## Installing

The installation of the program can be done using the following methods
listed by order of preference:

- Using the docker image `aliaume/polycheck-small:latest` available on Docker
  Hub.
- Using a `nix-shell` environment, by just running `nix-shell` in the root
  directory of the repository.
- Using the `nix` package manager, by running `nix-build polyreg.nix -A
  polyreg-exe` in the root directory of the repository.
- Using the `stack` Haskell build tool, by running `stack build` in the
  `polyreg` directory.

Note that the installation process requires the installation of external
solvers, which are included in the docker image and the nix derivation, but
cannot be build by the `stack` tool.

The easiest way is to use `docker run -it -p 3000:3000
aliaume/polycheck-small:latest polyreg-exe --web` to run the program in
a docker container which turns on the web interface.

## Building instructions

### For the paper

You will need a working LaTeX distribution, `pandoc`, `git` and the `make` tool
to compile the paper. To produce the PDF in its `lncs` format, run the
following command in the `paper` directory.

```bash
make polycheck.lncs.pdf
```

### For the model checker

You will need a working `stack` Haskell environment to compile the program.
Furthermore, the program calls solvers installed on the system, which can be
one of: `MONA`, `CVC5`, `Z3`, `Yices`, or `alt-ergo`. 

To compile the program, run the following command in the `polyreg` directory:

```bash
stack build
```

To run the tests, you can use the following command:

```bash
stack test
```


## Cite this repository

```bibtex
@software{LS2025,
    author  = {Lopez, Aliaume and Stefański, Rafał},
    title   = {Polyregular Functions and Model Checking},
    year    = {2025},
    url     = {https://github.com/AliaumeL/polyregular-model-checking},
    version = {0.0.1},
    date    = {2024-09-03},
}
```
