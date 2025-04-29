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
polycheck -i <input_file> -b <pre_condition_file> -a <post_condition_file>
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
polycheck --web
```

In order to run the `benchmark` mode, that runs the transformation
on the input (high-level) code and outputs various metrics on the
resulting simple-for programs and the generated first-order logic
specification, you can use the following command:

```bash
benchmarker -d ./assets/HighLevel/ > benchmarks.json
```

The JSON document will contain something similar to the document described below.

```json
{
    "benches": [
        {
            "bfName"   : "<filepath>",
            "bfHigh"   : {
                "bsBoolDepth" : 0,
                "bsDepth"     : 0,
                "bsSize"      : 0 
            },
            "bfSfp"    : {
                "Right" : {
                    "bsBoolDepth" : 0,
                    "bsDepth"     : 0,
                    "bsSize"      : 0
                }
            },
            "bfInterp" : {
                "Right" : {
                    "bsBoolDepth" : 0,
                    "bsDepth"     : 0,
                    "bsSize"      : 0
                }
            },
        }
        ...
    ]
}
```



## Installing

The installation of the program can be done using the following methods
listed by order of preference:

- Using the docker image `aliaume/polycheck-small:latest` available on Docker
  Hub.
- Using a `nix-shell` environment, by just running `nix-shell` in the root
  directory of the repository.
- Using the `nix` package manager, by running `nix-build polycheck.nix -A
  polycheck` in the root directory of the repository.
- Using the `stack` Haskell build tool in conjunction with `nix`
   by running `stack build --nix --nix-packages "zlib"` in the
  `polycheck` directory.
- Using the `stack` Haskell build tool, by running `stack build` in the
  `polycheck` directory.

Note that the installation process requires the installation of external
solvers, which are included in the docker image and the nix derivation, but
cannot be build by the `stack` tool. Namely, the following solvers can be used:
`MONA`, `CVC5`, `Z3`, `Yices`, and `alt-ergo`. The installation instructions
for these solvers can be found in their respective repositories. 

The easiest way is to use `docker run -it -p 3000:3000
aliaume/polycheck-small:latest polycheck --web` to run the program in
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

Then one can run the program using the following command:

```bash
stack exec polycheck -- -i <input_file> -b <pre_condition_file> -a <post_condition_file>
```

And the `benchmarker` using the following command:

```bash
stack exec benchmarker -- -d <high_level_assets_directory>
```

To test the web interface, you can run the following command:

```bash
stack exec polycheck -- --web
```

And then connect to `http://localhost:3000` in your web browser.

## Evaluating the code

### Recreating the tables from the paper

In order to recreate the tables from the paper, you need to run the `benchmarker` program
with the argument `--reproduce-table` and the number of the table you want to reproduce.

- `--reproduce-table 1` will reproduce Table 1, which gives the sizes of the intermediate
  and final representations of the tables. This takes around 15 minutes to run.
- `--reproduce-table 1l` will reproduce the light version of which does not include Table 1,
  skipping `bibtex.pr` and `litteral_test.pr`. This takes less than 1 second to run.
- `--reproduce-table 2` will reproduce Table 2, which verifies 5 example Hoare triples
  with timeout set to 5 seconds for each triple. It then reports on the results of the verification
  using Mona, CVC5 and Z3, as well as the size and quantifier rank of the formula fed to the solvers.
  This takes around 1 minute to run.
- `-- reproduce-table 2l` will reproduce the light version of Table 2 which only includes 1 easy example.
  This takes less than 1 second to run.

### Smoke test

The `benchmarker` program can be used to run a smoke test on the code. For this purpose we propose 
recreating table `1l` and `2l` with the following command:

```bash
stack run -- benchmarker --reproduce-table 1l
stack run -- benchmarker --reproduce-table 2l
```

This will run the smoke test on the code and check that everything is working as expected.

### Full evaluation

In order to run the full evaluation you can create a Table-1 style table with all the programs in
the `assets/HighLevel` directory and a Table-2 style table with all possible triples using the programs from `assets/HighLevel` and `assets/Formulas`. For this you can use the following commands:

- `stack run -- benchmarker -d assets/HighLevel` this takes around 10 min to run.
- `stack run -- benchmarker -d assets/HighLevel -f assets/Formulas` this is the heavy evaluation, which takes many hours to run.

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
