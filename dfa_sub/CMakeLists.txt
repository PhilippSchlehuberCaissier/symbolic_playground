cmake_minimum_required(VERSION 3.25)
project(sym_min)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall -fsanitize=address")
include_directories(/usr/local/include/spot/)
link_directories(/usr/local/lib/)

add_executable(ltlf2dfa main.cpp)
target_link_libraries(ltlf2dfa spot bddx)