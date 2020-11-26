cmake_minimum_required(VERSION 3.13)

set(PROJECT_NAME comm_test)
project(${PROJECT_NAME})

# Data files
file(GLOB INPUT_FILES ${PROJECT_SOURCE_DIR}/etc/*.txt)
list(JOIN INPUT_FILES " " TEST_DATA)

# Tests
enable_testing()
add_test(
    NAME comm
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm1
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-1.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm2
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-2.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm3
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-3.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm12
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-12.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm13
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-13.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm23
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-23.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
add_test(
    NAME comm123
    COMMAND sh -c "${PROJECT_SOURCE_DIR}/test-123.sh $<TARGET_FILE:comm> ${TEST_DATA}"
    )
