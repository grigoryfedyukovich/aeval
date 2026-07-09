cmake_minimum_required(VERSION 3.15)

if (POLICY CMP0167)
  cmake_policy(SET CMP0167 OLD)
endif()
if (POLICY CMP0135)
  cmake_policy(SET CMP0135 NEW)
endif()
if (POLICY CMP0074)
  cmake_policy(SET CMP0074 NEW)
endif()
if (POLICY CMP0144)
  cmake_policy(SET CMP0144 NEW)
endif()

project (FreqHorn)
set (FreqHorn_VERSION_MAJOR 0)
set (FreqHorn_VERSION_MINOR 5)

if (NOT PACKAGE_VERSION)
  set(PACKAGE_VERSION
    "${FreqHorn_VERSION_MAJOR}.${FreqHorn_VERSION_MINOR}.${FreqHorn_VERSION_PATCH}")
  if (DEFINED FreqHorn_VERSION_TWEAK)
    set (PACKAGE_VERSION "${PACKAGE_VERSION}-${FreqHorn_VERSION_TWEAK}")
  endif()
  set (FreqHorn_VERSION_INFO ${PACKAGE_VERSION})
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


option (FreqHorn_STATIC_EXE "Static executable." OFF)

set (CUSTOM_BOOST_ROOT "" CACHE PATH "Path to custom boost installation.")
set (GMP_SEARCH_PATH "" CACHE PATH "Search path for gmp.")
set (FREQHORN_LOCAL_DEPS "${CMAKE_BINARY_DIR}/deps" CACHE PATH "Build-tree dependency install prefix.")
if (NOT CUSTOM_BOOST_ROOT AND EXISTS "${FREQHORN_LOCAL_DEPS}/include/boost/version.hpp")
  set (CUSTOM_BOOST_ROOT "${FREQHORN_LOCAL_DEPS}" CACHE PATH "Path to custom boost installation." FORCE)
endif()
if (NOT GMP_SEARCH_PATH AND EXISTS "${FREQHORN_LOCAL_DEPS}/include/gmp.h")
  set (GMP_SEARCH_PATH "${FREQHORN_LOCAL_DEPS}" CACHE PATH "Search path for gmp." FORCE)
endif()
if (CUSTOM_BOOST_ROOT)
  set (BOOST_ROOT ${CUSTOM_BOOST_ROOT})
  set (Boost_NO_SYSTEM_PATHS "ON")
endif()

# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

include(ExternalProject)
set_property(DIRECTORY PROPERTY EP_STEP_TARGETS configure build test)

set (BOOST_VERSION "1.91.0")
set (BOOST_ARCHIVE "boost_1_91_0.tar.gz")
set (BOOST_URL "https://archives.boost.io/release/${BOOST_VERSION}/source/${BOOST_ARCHIVE}")
set (BOOST_SHA256 "5734305f40a76c30f951c9abd409a45a2a19fb546efe4162119250bbe4d3a463")
set (GMP_VERSION "6.3.0")
set (GMP_ARCHIVE "gmp-${GMP_VERSION}.tar.xz")
set (GMP_URL "https://gmplib.org/download/gmp/${GMP_ARCHIVE}")
set (GMP_SHA256 "a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898")
set (Z3_VERSION "4.16.0" CACHE STRING "Z3 version to build/use")
set (Z3_TAG "z3-${Z3_VERSION}" CACHE STRING "Z3 git tag to use")
set (Z3_REPO "https://github.com/Z3Prover/z3.git" CACHE STRING "Z3 repo")
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set (Z3_DEBUG "-d")
else()
  set (Z3_DEBUG "")
endif()

find_program(Z3_PYTHON_EXECUTABLE NAMES python3 python)
if (NOT Z3_PYTHON_EXECUTABLE)
  message(FATAL_ERROR "Could not find python3 or python for configuring Z3")
endif()

set (Z3_ENV PYTHONPYCACHEPREFIX=${CMAKE_BINARY_DIR}/z3-pycache)
if (APPLE)
  if (CMAKE_OSX_SYSROOT)
    if (IS_ABSOLUTE "${CMAKE_OSX_SYSROOT}")
      set (Z3_OSX_SYSROOT "${CMAKE_OSX_SYSROOT}")
    else()
      execute_process(
        COMMAND xcrun --sdk ${CMAKE_OSX_SYSROOT} --show-sdk-path
        OUTPUT_VARIABLE Z3_OSX_SYSROOT
        OUTPUT_STRIP_TRAILING_WHITESPACE)
    endif()
  else()
    execute_process(
      COMMAND xcrun --show-sdk-path
      OUTPUT_VARIABLE Z3_OSX_SYSROOT
      OUTPUT_STRIP_TRAILING_WHITESPACE)
  endif()
  if (Z3_OSX_SYSROOT)
    list (APPEND Z3_ENV SDKROOT=${Z3_OSX_SYSROOT})
  endif()
  if (CMAKE_OSX_DEPLOYMENT_TARGET)
    list (APPEND Z3_ENV MACOSX_DEPLOYMENT_TARGET=${CMAKE_OSX_DEPLOYMENT_TARGET})
  endif()
endif()

set (Boost_USE_STATIC_LIBS ON)
set (BOOST_COMPONENTS)
if (UNIT_TESTS)
  set (BOOST_COMPONENTS ${BOOST_COMPONENTS} unit_test_framework)
endif()
find_package (Boost ${BOOST_VERSION} QUIET COMPONENTS ${BOOST_COMPONENTS})
if (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
endif ()

find_package(Gmp ${GMP_VERSION} QUIET)
if (GMP_FOUND)
  include_directories (${GMP_INCLUDE_DIR})
  include_directories (${GMPXX_INCLUDE_DIR})
endif()

ExternalProject_Add(z3
  GIT_REPOSITORY  ${Z3_REPO}
  GIT_TAG ${Z3_TAG}
  BUILD_IN_SOURCE 1
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CONFIGURE_COMMAND ${CMAKE_COMMAND} -E env CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} PYTHON=${Z3_PYTHON_EXECUTABLE} ${Z3_ENV}
  ./configure -p <INSTALL_DIR> -b build --staticlib ${Z3_DEBUG}
  BUILD_COMMAND ${CMAKE_COMMAND} -E env ${Z3_ENV} make -j3 -C build
  INSTALL_COMMAND ${CMAKE_COMMAND} -E env ${Z3_ENV} make -C build install
  COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_INSTALL 1
  LOG_BUILD 1)

find_package(Z3 ${Z3_VERSION} QUIET)

set (MISSING_DEPS "")
if (NOT Boost_FOUND)
  set (BOOST_CONFIGURE_COMMAND ${CMAKE_COMMAND} -E true)
  set (BOOST_BUILD_COMMAND ${CMAKE_COMMAND} -E true)
  set (BOOST_INSTALL_COMMAND
    ${CMAKE_COMMAND} -E make_directory <INSTALL_DIR>/include
    COMMAND ${CMAKE_COMMAND} -E copy_directory <SOURCE_DIR>/boost <INSTALL_DIR>/include/boost)
  if (UNIT_TESTS)
    set (BOOST_CONFIGURE_COMMAND ./bootstrap.sh --prefix=<INSTALL_DIR> --with-libraries=test)
    set (BOOST_BUILD_COMMAND ${CMAKE_COMMAND} -E true)
    set (BOOST_INSTALL_COMMAND
      ./b2 -j3 variant=release link=static runtime-link=shared threading=multi --with-test install)
  endif()
  ExternalProject_Add(boost
    URL ${BOOST_URL}
    URL_HASH SHA256=${BOOST_SHA256}
    BUILD_IN_SOURCE 1
    INSTALL_DIR ${FREQHORN_LOCAL_DEPS}
    CONFIGURE_COMMAND ${BOOST_CONFIGURE_COMMAND}
    BUILD_COMMAND ${BOOST_BUILD_COMMAND}
    INSTALL_COMMAND ${BOOST_INSTALL_COMMAND}
    LOG_CONFIGURE 1
    LOG_INSTALL 1)
  list (APPEND MISSING_DEPS Boost)
endif()

if (NOT GMP_FOUND)
  ExternalProject_Add(gmp
    URL ${GMP_URL}
    URL_HASH SHA256=${GMP_SHA256}
    BUILD_IN_SOURCE 1
    INSTALL_DIR ${FREQHORN_LOCAL_DEPS}
    CONFIGURE_COMMAND ./configure --prefix=<INSTALL_DIR> --enable-cxx --disable-shared --enable-static
    BUILD_COMMAND make -j3
    INSTALL_COMMAND make install
    LOG_CONFIGURE 1
    LOG_BUILD 1
    LOG_INSTALL 1)
  list (APPEND MISSING_DEPS GMP)
endif()

if (NOT Z3_FOUND)
  ExternalProject_Get_Property (z3 INSTALL_DIR)
  set(Z3_ROOT ${INSTALL_DIR} CACHE PATH "Forced location of Z3" FORCE)
  list (APPEND MISSING_DEPS Z3)
endif()

if (MISSING_DEPS)
  set (CUSTOM_BOOST_ROOT "${FREQHORN_LOCAL_DEPS}" CACHE PATH "Path to custom boost installation." FORCE)
  set (GMP_SEARCH_PATH "${FREQHORN_LOCAL_DEPS}" CACHE PATH "Search path for gmp." FORCE)
  string(REPLACE ";" ", " MISSING_DEPS_MSG "${MISSING_DEPS}")
  message(WARNING
    "Missing dependencies: ${MISSING_DEPS_MSG}. Run\n"
    "\tcmake --build ${CMAKE_BINARY_DIR}\n"
    "then re-run CMake from ${CMAKE_BINARY_DIR}:\n"
    "\tcmake ${CMAKE_SOURCE_DIR}\n"
    "to continue configuring FreqHorn.")
  return()
endif()

set_target_properties(z3 PROPERTIES EXCLUDE_FROM_ALL ON)
include_directories(${Z3_INCLUDE_DIR})
message ("Found Z3 at ${Z3_EXECUTABLE}")
# indicate that we want z3 binary to be included in the binary distribution
install (PROGRAMS ${Z3_EXECUTABLE} DESTINATION bin)

install (FILES ${CMAKE_CURRENT_SOURCE_DIR}/README.md DESTINATION .)
# install all the licenses
install (FILES  ${CMAKE_CURRENT_SOURCE_DIR}/license.txt
  DESTINATION share/doc/FreqHorn
  RENAME FreqHorn_license.txt)

if (EXISTS z3-prefix/src/z3/LICENSE.txt)
  install (
    FILES
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/LICENSE.txt
    DESTINATION share/doc/FreqHorn
    RENAME z3_license.txt)
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

find_package(OpenMP)
if (OPENMP_FOUND)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
  #set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fopenmp")
endif()

find_package(Armadillo)
if (ARMADILLO_FOUND)
  add_definitions(-DHAVE_ARMADILLO)
  include_directories(${ARMADILLO_INCLUDE_DIR})
endif()  

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
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
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
