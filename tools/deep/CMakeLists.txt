add_executable (deephorn DeepHorn.cpp)
target_link_libraries (deephorn ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (deephorn bitwriter)
install(TARGETS deephorn RUNTIME DESTINATION bin)
