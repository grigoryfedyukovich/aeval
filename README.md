FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on the Expression library of <a href="http://seahorn.github.io/">SeaHorn</a> and the <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines probabilistic and syntax-guided methods to sample candidate invariants and checks their inductiveness / safety. Find more details at the FMCAD'17 <a href="http://www.cs.princeton.edu/~grigoryf/freqhorn.pdf">paper</a> and <a href="http://www.cs.princeton.edu/~grigoryf/freqhorn_slides.pdf">slides</a>.

News
====

A more efficient release (FreqHorn-2) is now available. It features a two-stage process: 1) deterministic bootstrapping with interpolation-based proofs of bounded safety, 2) nondeterministic sampling with the inductive subset extraction and on-demand exploiting of counterexamples-to-induction. Find more details at the TACAS'18 <a href="http://www.cs.princeton.edu/~grigoryf/freqhorn_followup.pdf">paper</a> (<a href="http://www.cs.princeton.edu/~grigoryf/freqhorn_tacas_slides.pdf">slides</a>).

Installation
============

Compiles with gcc-5 (on Linux) and clang-900 (on Mac). Assumes preinstalled Svn, Gmp, and Boost (libboost-system1.55-dev) packages. Additionally, armadillo package to get candidates from behaviors. 

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make` (again) to build FreqHorn

The binary of FreqHorn can be found at `build/tools/nonlin/`.
Run `./tools/deep/freqn --help` for the usage info.

MinimizIng Generated Invariants
========================

Solutions discovered by FreqHorn can be further minimized using the FreqHorn-IVC utility:

* `make ivc` to build FreqHorn-IVC

The binary of FreqHorn-IVC can be found at `build/tools/ivc/`.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which FreqHorn is expected to diverge.

Parallel Solver
===============

MPI-based version of FreqHorn can be found at the <a href="https://github.com/grigoryfedyukovich/aeval/tree/rnd-parallel-master-slave">rnd-parallel-master-slave</a> branch.

