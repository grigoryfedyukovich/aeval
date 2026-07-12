add_executable (tg TG.cpp)
target_link_libraries (tg ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
install(TARGETS tg RUNTIME DESTINATION bin)
