add_executable (term TerminationCheck.cpp)
target_link_libraries (term ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS term RUNTIME DESTINATION bin)
