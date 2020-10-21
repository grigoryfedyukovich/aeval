add_executable (chc CHC.cpp)
target_link_libraries (chc ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (chc bitwriter)
install(TARGETS chc RUNTIME DESTINATION bin)
