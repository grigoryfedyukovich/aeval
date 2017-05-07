cmake_minimum_required(VERSION 2.8.11)

project (SeaHorn)
set (SeaHorn_VERSION_MAJOR 0)
set (SeaHorn_VERSION_MINOR 1)
set (SeaHorn_VERSION_PATCH 0)
set (SeaHorn_VERSION_TWEAK "rc3")

if (NOT PACKAGE_VERSION)
  set(PACKAGE_VERSION
    "${SeaHorn_VERSION_MAJOR}.${SeaHorn_VERSION_MINOR}.${SeaHorn_VERSION_PATCH}")
  if (DEFINED SeaHorn_VERSION_TWEAK)
    set (PACKAGE_VERSION "${PACKAGE_VERSION}-${SeaHorn_VERSION_TWEAK}")
  endif()
  set (SeaHorn_VERSION_INFO ${PACKAGE_VERSION})
endif()


if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR )
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")
endif()

enable_testing()
include (CTest)

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake")


option (SEAHORN_STATIC_EXE "Static executable." OFF)

set (CUSTOM_BOOST_ROOT "" CACHE PATH "Path to custom boost installation.")
if (CUSTOM_BOOST_ROOT)
  set (BOOST_ROOT ${CUSTOM_BOOST_ROOT})
  set (Boost_NO_SYSTEM_PATHS "ON")
endif()

# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})


set (Boost_USE_STATIC_LIBS ON)
set (BOOST_COMPONENTS system mpi serialization)
if (UNIT_TESTS)
  set (BOOST_COMPONENTS ${BOOST_COMPONENTS} unit_test_framework)
endif()
  find_package (Boost 1.55 REQUIRED COMPONENTS ${BOOST_COMPONENTS})
if (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
endif ()

# Require MPI for this project:
find_package(MPI REQUIRED)
set(CMAKE_CXX_COMPILE_FLAGS ${CMAKE_CXX_COMPILE_FLAGS} ${MPI_COMPILE_FLAGS})
set(CMAKE_CXX_LINK_FLAGS ${CMAKE_CXX_LINK_FLAGS} ${MPI_LINK_FLAGS})
include_directories(${MPI_INCLUDE_PATH})

include(ExternalProject)
set_property(DIRECTORY PROPERTY EP_STEP_TARGETS configure build test)

set (Z3_TAG "origin/spacer3" CACHE STRING "Z3 git tag to use")
set (Z3_REPO "https://bitbucket.org/spacer/code.git" CACHE STRING "Z3 repo")
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set (Z3_DEBUG "-d")
else()
  set (Z3_DEBUG "")
endif()

ExternalProject_Add(z3
  GIT_REPOSITORY  ${Z3_REPO}
  GIT_TAG ${Z3_TAG}
  BUILD_IN_SOURCE 1
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CONFIGURE_COMMAND env CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER}
  ./configure -p <INSTALL_DIR> -b build --staticlib ${Z3_DEBUG}
  BUILD_COMMAND make -j3 -C build
  INSTALL_COMMAND make -C build install
  COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_INSTALL 1
  LOG_BUILD 1)

find_package(Z3 4.3.2)
if (NOT Z3_FOUND)
  ExternalProject_Get_Property (z3 INSTALL_DIR)
  set(Z3_ROOT ${INSTALL_DIR} CACHE PATH "Forced location of Z3" FORCE)
  message(WARNING "No Z3 found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
else()
  set_target_properties(z3 PROPERTIES EXCLUDE_FROM_ALL ON)
  include_directories(${Z3_INCLUDE_DIR})
  message ("Found Z3 at ${Z3_EXECUTABLE}")
  # indicate that we want z3 binary to be included in the binary distribution
  install (PROGRAMS ${Z3_EXECUTABLE} DESTINATION bin)
endif()

ExternalProject_Add (llvm
  SVN_REPOSITORY http://llvm.org/svn/llvm-project/llvm/tags/RELEASE_360/final/
  SOURCE_DIR ${CMAKE_SOURCE_DIR}/ext/llvm
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CMAKE_ARGS
  -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER} -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
  -DCMAKE_BUILD_TYPE:STRING=${CMAKE_BUILD_TYPE}
  -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
  -DLLVM_TARGETS_TO_BUILD:STRING=X86 -DWITH_POLY:BOOL=OFF
  -DLLVM_ENABLE_PEDANTIC=OFF
  -DLLVM_ENABLE_PIC=ON -DLLVM_REQUIRES_RTTI:BOOL=TRUE
  TEST_AFTER_INSTALL 1
  TEST_COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_BUILD 1
  LOG_INSTALL 1)

find_package (LLVM 3.6.0 CONFIG NO_DEFAULT_PATH)
if (NOT LLVM_FOUND)
  ExternalProject_Get_Property (llvm INSTALL_DIR)
  set (LLVM_ROOT ${INSTALL_DIR})
  set (LLVM_DIR ${LLVM_ROOT}/share/llvm/cmake CACHE PATH
    "Forced location of LLVM cmake config" FORCE)
  message (WARNING "No llvm found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
  return()
else()
  set_target_properties(llvm PROPERTIES EXCLUDE_FROM_ALL ON)

  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

  # We incorporate the CMake features provided by LLVM:
  list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
  include(AddLLVM)
  include(HandleLLVMOptions)
  set(LLVM_RUNTIME_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/${CMAKE_CFG_INTDIR}/bin)
  set(LLVM_LIBRARY_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/${CMAKE_CFG_INTDIR}/lib)

  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_CXXFLAGS}")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LLVM_LDFLAGS}")

  set(LLVM_REQUIRES_RTTI TRUE)
  set(LLVM_REQUIRES_EH TRUE)

  include_directories(${LLVM_INCLUDE_DIRS})
  link_directories(${LLVM_LIBRARY_DIRS})
  add_definitions(${LLVM_DEFINITIONS})

endif()


install (FILES ${CMAKE_CURRENT_SOURCE_DIR}/README.md DESTINATION .)
# install all the licenses
install (FILES  ${CMAKE_CURRENT_SOURCE_DIR}/license.txt
  DESTINATION share/doc/seahorn
  RENAME seahorn_license.txt)

if (EXISTS z3-prefix/src/z3/LICENSE.txt)
  install (
    FILES
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/LICENSE.txt
    DESTINATION share/doc/seahorn
    RENAME z3_license.txt)
endif()

if (EXISTS ${CMAKE_CURRENT_BINARY_DIR}/llvm-prefix/src/llvm-build/bin/clang-3.6)
  install (
    PROGRAMS
    ${CMAKE_CURRENT_BINARY_DIR}/llvm-prefix/src/llvm-build/bin/clang-3.6
    DESTINATION bin)
endif()

if (EXISTS ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build)
  file(GLOB z3py
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.py?
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.py?
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.so
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.dylib
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.dll
    )
  install(FILES ${z3py} DESTINATION lib/z3py)
endif()

find_package(Gmp REQUIRED)
if (GMP_FOUND)
  include_directories (${GMP_INCLUDE_DIR})
  include_directories (${GMPXX_INCLUDE_DIR})
else()
  set(GMP_LIB "")
  set(GMPXX_LIB "")
endif()

find_package(OpenMP)
IF(OPENMP_FOUND)
  SET(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
  SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
ENDIF()

install(DIRECTORY include/
  DESTINATION include
  FILES_MATCHING
  PATTERN "*.hpp"
  PATTERN "*.hh"
  PATTERN "*.h"
  PATTERN ".svn" EXCLUDE
  )

install(DIRECTORY ${CMAKE_BINARY_DIR}/include/
  DESTINATION include
  FILES_MATCHING
  PATTERN "*.hpp"
  PATTERN "*.hh"
  PATTERN "*.h"
  PATTERN "CMakeFiles" EXCLUDE
  PATTERN ".svn" EXCLUDE
  )

set(CMAKE_CXX_EXTENSIONS ON)
add_definitions(-Wno-redeclared-class-member -Wno-sometimes-uninitialized)
add_definitions(-Wno-covered-switch-default)
add_definitions(-Wno-inconsistent-missing-override)
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  add_definitions( -Wthread-safety)
  if (CMAKE_BUILD_TYPE STREQUAL "Debug")
    add_definitions(-fsanitize=address -fno-omit-frame-pointer)
    SET(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=address")
  endif()
endif()
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  add_definitions( -Wno-unused-local-typedefs)
endif ()

# add the include directory from the build tree
include_directories(BEFORE ${CMAKE_CURRENT_BINARY_DIR}/include)

### add our include directories to the front, overriding directories
### specified by external packages.
include_directories(BEFORE
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/include)

add_subdirectory(tools)
