cmake_minimum_required(VERSION 3.13)

include(test/Strict.cmake)

set(PROJECT_NAME md_handler)
project(${PROJECT_NAME})

# Set up the compiler flags
set(CMAKE_CXX_FLAGS "-g")
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Include directories
set(COMMON_INCLUDES ${PROJECT_SOURCE_DIR}/include)
include_directories(${COMMON_INCLUDES})

# Source files
file(GLOB SRC_FILES ${PROJECT_SOURCE_DIR}/src/*.cpp)

# Separate executable: main
list(REMOVE_ITEM SRC_FILES ${PROJECT_SOURCE_DIR}/src/main.cpp)

# Compile source files into a library
add_library(md_handler_lib ${SRC_FILES})
target_compile_options(md_handler_lib PUBLIC ${COMPILE_OPTS})
target_link_options(md_handler_lib PUBLIC ${LINK_OPTS})

# Main is separate
add_executable(md_handler ${PROJECT_SOURCE_DIR}/src/main.cpp)
target_compile_options(md_handler PRIVATE ${COMPILE_OPTS})
target_link_options(md_handler PRIVATE ${LINK_OPTS})

# linking Main against the library
target_link_libraries(md_handler md_handler_lib)

# google test is a git submodule
add_subdirectory(googletest)

# google benchmark is a git submodule
add_subdirectory(googlebenchmark)

# test and benchmark submodule
add_subdirectory(test)

enable_testing()
add_test(NAME tests COMMAND runUnitTests)
