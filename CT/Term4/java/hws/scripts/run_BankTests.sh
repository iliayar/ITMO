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

echo "Sources: " $SOURCES

LIB_FOLDER="${ROOT}/lib"
JUNIT="${LIB_FOLDER}/junit-4.11.jar"
HAMCREST="${LIB_FOLDER}/hamcrest-core-1.3.jar"

echo "Junit path: ${JUNIT}"
echo "Hamcrest path: ${HAMCREST}"

javac -cp "${JUNIT}:${HAMCREST}" -d . $SOURCES || abort
java -cp ".:${JUNIT}:${HAMCREST}" "info.kgeorgiy.ja.yaroshevskij.bank.BankTests"
RET=$?
cleanup
exit $RET
