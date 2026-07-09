FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines syntax-guided methods to inductive invariant synthesis with data learning and quantified reasoning over arrays. Find more details at <a href="http://www.cs.fsu.edu/~grigory/freqhorn-arrays.pdf">CAV'19</a> and <a href="http://www.cs.fsu.edu/~grigory/multi-freqhorn.pdf">FMCAD'18</a> papers.

Installation
============

Compiles as C++14. CMake builds Boost 1.91.0, <a href="https://gmplib.org/">GMP</a> 6.3.0, and Z3 4.16.0 from source when they are missing or too old. Z3 4.16.0 needs a recent C++ standard library; on Ubuntu 22.04, use GCC/G++ 13 or newer. Additionally, install the Armadillo package to get candidates from behaviors.

On Ubuntu 22.04, a typical setup is:

* `sudo apt update`
* `sudo apt install -y software-properties-common build-essential libarmadillo-dev`
* `sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test`
* `sudo apt update`
* `sudo apt install -y gcc-13 g++-13`

Out-of-tree build:

* `mkdir build ; cd build`
* `cmake .. -DCMAKE_C_COMPILER=/usr/bin/gcc-13 -DCMAKE_CXX_COMPILER=/usr/bin/g++-13 -DCMAKE_PREFIX_PATH=$PWD/deps -DZ3_VERSION=4.16.0 -DZ3_TAG=z3-4.16.0`
* `cmake --build .` to build missing dependencies
* `cmake .. -DCMAKE_C_COMPILER=/usr/bin/gcc-13 -DCMAKE_CXX_COMPILER=/usr/bin/g++-13 -DCMAKE_PREFIX_PATH=$PWD/deps -DZ3_VERSION=4.16.0 -DZ3_TAG=z3-4.16.0` again if CMake stopped after installing missing dependencies
* `cmake --build .` again to build FreqHorn

The binary of FreqHorn can be found at `build/tools/deep/`.
Run `freqhorn --help` for the usage info.

FreqHorn does not automatically find counterexamples (unless the CHC system can be trivially simplified), but its supplementary tool `expl` tool does. We recommend running `freqhorn` and `expl` concurrently.

The tools print `Success ...` if the system is satisfiable.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn` and `bench_horn_multiple`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which `freqhorn` is expected to diverge (but `expl` should find counterexamples).
