add_executable (aeval Ae.cpp)
target_link_libraries (aeval ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS aeval RUNTIME DESTINATION bin)
