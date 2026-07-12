TG
==

Test-generation tooling for constrained Horn clauses (CHC) based on the Z3 SMT solver.

Publications
============

* <a href="https://doi.org/10.1007/978-3-031-78750-8_7">ATVA'24</a>
* <a href="https://doi.org/10.1007/978-3-030-99527-0_14">TACAS'22</a>


Installation
============

Compiles as C++14. CMake builds Boost 1.91.0, GMP 6.3.0, and Z3 4.16.0 from source when they are missing or too old. Z3 4.16.0 needs a recent C++ standard library; on Ubuntu 22.04, use GCC/G++ 13 or newer.

On Ubuntu 22.04, a typical setup is:

* `sudo apt update`
* `sudo apt install -y software-properties-common build-essential`
* `sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test`
* `sudo apt update`
* `sudo apt install -y gcc-13 g++-13`

Out-of-tree build:

* `mkdir build ; cd build`
* `cmake .. -DCMAKE_C_COMPILER=/usr/bin/gcc-13 -DCMAKE_CXX_COMPILER=/usr/bin/g++-13 -DCMAKE_PREFIX_PATH=$PWD/deps -DZ3_VERSION=4.16.0 -DZ3_TAG=z3-4.16.0`
* `cmake --build .` to build missing dependencies
* `cmake .. -DCMAKE_C_COMPILER=/usr/bin/gcc-13 -DCMAKE_CXX_COMPILER=/usr/bin/g++-13 -DCMAKE_PREFIX_PATH=$PWD/deps -DZ3_VERSION=4.16.0 -DZ3_TAG=z3-4.16.0` again if CMake stopped after installing missing dependencies
* `cmake --build .` again to build the tools

The TG binary can be found at `build/tools/tg/`.
Run `tg --help` for the usage info.

Benchmarks
==========

Collection of SMT-LIB2 translations can be found in the benchmark directories.
