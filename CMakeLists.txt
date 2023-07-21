cmake_minimum_required(VERSION 3.25)
project(sym_min)

set(CMAKE_CXX_STANDARD 20)
include_directories(/usr/local/include/spot/)
link_directories(/usr/local/lib/)

add_executable(sym_min main.cpp)
target_link_libraries(sym_min spot bddx)