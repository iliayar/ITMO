#!/usr/bin/env bash 

ROOT="${PWD}/$(dirname $0)/.."
DIR="${PWD}"

function cleanup() {
    cd "${ROOT}"
    rm -Rf "${BUILD_DIR}"
}

function abort() {
    cleanup
    exit 1
}

cd "${ROOT}" || abort

BUILD_DIR=$(mktemp -d --tmpdir=${ROOT}/)

cd "${BUILD_DIR}" || abort

SOURCES=$(find "../java-solutions/info/kgeorgiy/ja/yaroshevskij/bank" -type f -name '*.java')

echo "Files to compile: " $SOURCES

LIB_FOLDER="${ROOT}/lib"
JUNIT="${LIB_FOLDER}/junit-4.11.jar"
HAMCREST="${LIB_FOLDER}/hamcrest-core-1.3.jar"

echo "Junit path: ${JUNIT}"
echo "Hamcrest path: ${HAMCREST}"

javac -cp "${JUNIT}:${HAMCREST}" -d . $SOURCES || abort

TESTS=(
    BankTest
    ClientTest    
)

FULL_TESTS=()
for test in ${TESTS[@]}; do
    FULL_TESTS+=("info.kgeorgiy.ja.yaroshevskij.bank.test.${test}")
done
echo "Running tests: " ${FULL_TESTS[@]}
java -cp ".:${JUNIT}:${HAMCREST}" "org.junit.runner.JUnitCore" ${FULL_TESTS[@]}
cleanup
