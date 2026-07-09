FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines syntax-guided methods to inductive invariant synthesis with data learning and quantified reasoning over arrays. Find more details at <a href="http://www.cs.fsu.edu/~grigory/freqhorn-arrays.pdf">CAV'19</a> and <a href="http://www.cs.fsu.edu/~grigory/multi-freqhorn.pdf">FMCAD'18</a> papers.

Installation
============

Compiles as C++14 with gcc-7 (on Linux) and clang-1001 (on Mac). CMake builds Boost 1.91.0, <a href="https://gmplib.org/">GMP</a> 6.3.0, and Z3 4.16.0 from source when they are missing or too old. Additionally, armadillo package to get candidates from behaviors.

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build missing dependencies
* `make` (again) to build FreqHorn

The binary of FreqHorn can be found at `build/tools/deep/`.
Run `freqhorn --help` for the usage info.

FreqHorn does not automatically find counterexamples (unless the CHC system can be trivially simplified), but its supplementary tool `expl` tool does. We recommend running `freqhorn` and `expl` concurrently.

The tools print `Success ...` if the system is satisfiable.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn` and `bench_horn_multiple`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which `freqhorn` is expected to diverge (but `expl` should find counterexamples).
