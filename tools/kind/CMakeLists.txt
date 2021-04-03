add_executable (kind KInduction.cpp)
target_link_libraries (kind ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS kind RUNTIME DESTINATION bin)
