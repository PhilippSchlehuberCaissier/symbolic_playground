cmake_minimum_required(VERSION 3.25)
project(sym_min)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall -fsanitize=address")
include_directories(/usr/local/include/spot/)
link_directories(/usr/local/lib/)

add_library(nfahelp SHARED nfa_helper.cpp)

add_library(nfatrans SHARED nfa_translate.cpp)

add_executable(ltlf2dfa main.cpp)
target_link_libraries(ltlf2dfa PUBLIC spot PUBLIC bddx PUBLIC nfahelp PUBLIC nfatrans)


# Set the path to the Catch2 library
#set(Catch2_DIR "/path/to/catch2/installation")

# Find Catch2
find_package(Catch2 REQUIRED)

message(STATUS "CATCH2: ${Catch2_INCLUDE_DIRS}")

# Add the executables for the tests
add_executable(TestTrans tests/test_trans.cpp)
#add_executable(Test2 test2.cpp)

# Link Catch2 and the library to the test executables
target_link_libraries(TestTrans PRIVATE Catch2::Catch2WithMain PUBLIC nfatrans PUBLIC nfahelp PUBLIC spot PUBLIC bddx)
#target_link_libraries(Test2 PRIVATE Catch2::Catch2WithMain MyLibrary)

# Enable testing
include(Catch)
catch_discover_tests(TestTrans)
#catch_discover_tests(Test2)
