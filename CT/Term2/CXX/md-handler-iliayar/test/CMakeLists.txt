cmake_minimum_required(VERSION 3.13)

# root includes
set(ROOT_INCLUDES ${PROJECT_SOURCE_DIR}/include)

set(PROJECT_NAME md_handler_test)
project(${PROJECT_NAME})

# Inlcude directories
include_directories(${ROOT_INCLUDES})

# Include the gtest library
include_directories(${gtest_SOURCE_DIR}/include ${gtest_SOURCE_DIR}
                    ${gmock_SOURCE_DIR}/include ${gmock_SOURCE_DIR})

# Source files
file(GLOB SRC_FILES ${PROJECT_SOURCE_DIR}/src/*.h
                    ${PROJECT_SOURCE_DIR}/src/*.cpp)

# Unit tests
add_executable(runUnitTests ${SRC_FILES})
target_compile_options(runUnitTests PRIVATE ${COMPILE_OPTS}
    -Wno-gnu-zero-variadic-macro-arguments -Wno-unused-function -Wno-missing-braces)
target_link_options(runUnitTests PRIVATE ${LINK_OPTS})

# Standard linking to gtest stuff
target_link_libraries(runUnitTests gtest gtest_main gmock_main)

# Extra linking for the project
target_link_libraries(runUnitTests md_handler_lib)

# Benchmark config
file(GLOB BENCHMARK_SRC_FILES ${PROJECT_SOURCE_DIR}/benchmark/*.h
                              ${PROJECT_SOURCE_DIR}/benchmark/*.cpp)

add_executable(runBenchmarkTests ${BENCHMARK_SRC_FILES})
target_compile_options(runBenchmarkTests PRIVATE ${COMPILE_OPTS}
    -Wno-gnu-zero-variadic-macro-arguments -Wno-unused-function -Wno-missing-braces)
target_link_options(runBenchmarkTests PRIVATE ${LINK_OPTS})

target_link_libraries(runBenchmarkTests md_handler_lib)
target_link_libraries(runBenchmarkTests benchmark::benchmark)
