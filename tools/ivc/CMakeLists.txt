add_executable (ivc Ivc.cpp)
target_link_libraries (ivc ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS ivc RUNTIME DESTINATION bin)
