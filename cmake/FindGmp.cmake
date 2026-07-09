if (NOT GMP_FOUND)
  set(GMP_SEARCH_PATH "" CACHE PATH "Search path for gmp.")
  find_path(GMP_INCLUDE_DIR NAMES gmp.h PATHS ${GMP_SEARCH_PATH}/include)
  find_library(GMP_LIB NAMES gmp PATHS ${GMP_SEARCH_PATH}/lib)
  
  find_path(GMPXX_INCLUDE_DIR NAMES gmpxx.h PATHS ${GMP_SEARCH_PATH}/include)
  find_library(GMPXX_LIB NAMES gmpxx PATHS ${GMP_SEARCH_PATH}/lib)

  if (GMP_INCLUDE_DIR AND EXISTS "${GMP_INCLUDE_DIR}/gmp.h")
    file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" GMP_VERSION_MAJOR_LINE
      REGEX "^#define[ \t]+__GNU_MP_VERSION[ \t]+[0-9]+")
    file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" GMP_VERSION_MINOR_LINE
      REGEX "^#define[ \t]+__GNU_MP_VERSION_MINOR[ \t]+[0-9]+")
    file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" GMP_VERSION_PATCH_LINE
      REGEX "^#define[ \t]+__GNU_MP_VERSION_PATCHLEVEL[ \t]+[0-9]+")
    string(REGEX REPLACE "^#define[ \t]+__GNU_MP_VERSION[ \t]+([0-9]+).*" "\\1"
      GMP_VERSION_MAJOR "${GMP_VERSION_MAJOR_LINE}")
    string(REGEX REPLACE "^#define[ \t]+__GNU_MP_VERSION_MINOR[ \t]+([0-9]+).*" "\\1"
      GMP_VERSION_MINOR "${GMP_VERSION_MINOR_LINE}")
    string(REGEX REPLACE "^#define[ \t]+__GNU_MP_VERSION_PATCHLEVEL[ \t]+([0-9]+).*" "\\1"
      GMP_VERSION_PATCH "${GMP_VERSION_PATCH_LINE}")
    set(GMP_VERSION_STRING "${GMP_VERSION_MAJOR}.${GMP_VERSION_MINOR}.${GMP_VERSION_PATCH}")
  endif()

  mark_as_advanced(GMP_SEARCH_PATH 
    GMP_INCLUDE_DIR GMP_LIB GMPXX_INCLUDE_DIR GMPXX_LIB GMP_VERSION_STRING)

  include (FindPackageHandleStandardArgs)
  find_package_handle_standard_args(Gmp
    REQUIRED_VARS GMP_INCLUDE_DIR GMP_LIB GMPXX_INCLUDE_DIR GMPXX_LIB
    VERSION_VAR GMP_VERSION_STRING)
endif()
