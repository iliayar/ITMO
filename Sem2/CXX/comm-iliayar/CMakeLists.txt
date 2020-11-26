cmake_minimum_required(VERSION 3.13)

include(test/Strict.cmake)

set(PROJECT_NAME comm)
project(${PROJECT_NAME})

# Set up the compiler flags
set(CMAKE_CXX_FLAGS "-g")
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Inlcude directories
set(COMMON_INCLUDES ${PROJECT_SOURCE_DIR}/include)
include_directories(${COMMON_INCLUDES})

# Main
add_executable(comm ${PROJECT_SOURCE_DIR}/src/main.cpp)
target_compile_options(comm PRIVATE ${COMPILE_OPTS})
target_link_options(comm PRIVATE ${LINK_OPTS})

# Tests
add_subdirectory(test)
