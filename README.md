# LazyHorn
A lazy and incremental framework for solving constrained horn clauses

## Building using CMake
Run the following in the top level directory of the repository.
```
mkdir build
cd build
cmake -G "Unix Makefiles" ../
make
```

## Dependencies
* [The program_options library in the Boost C++ libraries](https://www.boost.org/doc/libs/1_79_0/doc/html/program_options.html)
* [The Z3 Theorem Prover](https://github.com/Z3Prover/z3)

Paths to custom installation folders of the above libraries can be updated in `LazyHorn/CMakeLists.txt` and `LazyHorn/cmake/FindZ3.cmake`.
