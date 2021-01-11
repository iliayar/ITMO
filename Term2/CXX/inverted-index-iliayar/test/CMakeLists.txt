cmake_minimum_required(VERSION 3.13)

# root includes
set(ROOT_INCLUDES ${PROJECT_SOURCE_DIR}/include)

set(PROJECT_NAME search_engine_test)
project(${PROJECT_NAME})

# Inlcude directories
include_directories(${ROOT_INCLUDES})

# Source files
file(GLOB SRC_FILES ${PROJECT_SOURCE_DIR}/src/*.cpp)

# Include the gtest library
include_directories(${gtest_SOURCE_DIR}/include ${gtest_SOURCE_DIR})

# Unit tests
add_executable(runUnitTests ${SRC_FILES})
target_compile_options(runUnitTests PRIVATE ${COMPILE_OPTS}
    -Wno-gnu-zero-variadic-macro-arguments -Wno-unused-function -Wno-missing-braces -Wno-unused-value)
target_link_options(runUnitTests PRIVATE ${LINK_OPTS})

# Standard linking to gtest stuff
target_link_libraries(runUnitTests gtest gtest_main)

# Extra linking for the project
target_link_libraries(runUnitTests search_engine_lib)

# Data files
file(GLOB ETC_FILES RELATIVE ${PROJECT_SOURCE_DIR} ${PROJECT_SOURCE_DIR}/etc/*)

# Copy data files for tests
add_custom_command(
    OUTPUT ${ETC_FILES}
    COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/etc ${CMAKE_CURRENT_BINARY_DIR}/etc
    DEPENDS ${ETC_FILES}
    COMMENT "Copying test data")

add_custom_target(
    etc DEPENDS ${ETC_FILES})

add_dependencies(runUnitTests etc)
