set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wno-deprecated-register")

project(calc CXX)

cmake_minimum_required(VERSION 3.1)

find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

BISON_TARGET(calc_parser
             calc_parser.yy
             ${CMAKE_CURRENT_BINARY_DIR}/calc_parser.tab.cc)
FLEX_TARGET(calc_lexer
            calc_lexer.l
            ${CMAKE_CURRENT_BINARY_DIR}/calc_lexer.yy.cc)
ADD_FLEX_BISON_DEPENDENCY(calc_lexer calc_parser)

add_executable(calc
    main.cpp
    calc_driver.cpp

    ${FLEX_calc_lexer_OUTPUTS}
    ${BISON_calc_parser_OUTPUTS}
)
target_include_directories(calc
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${FLEX_INCLUDE_DIRS}
        ${CMAKE_CURRENT_BINARY_DIR})
set_property(TARGET calc
             PROPERTY CXX_STANDARD 14)
