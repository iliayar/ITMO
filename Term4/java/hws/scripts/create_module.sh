#!/usr/bin/env bash

ROOT="${PWD}/$(dirname $0)/.."
DIR="${PWD}"

cd "${ROOT}"

BUILD_DIR=$(mktemp -d --tmpdir=${ROOT}/)
MODULE="info.kgeorgiy.ja.yaroshevskij.implementor"
PACKAGE="info.kgeorgiy.ja.yaroshevskij.implementor"
PACKAGE_PATH="$(echo "${PACKAGE}" | tr '.' '/')"
MODULE_PATH="${ROOT}/../java-advanced-2021/artifacts/:${ROOT}/../java-advanced-2021/lib/"
ARTIFACTS_FOLDER="artifacts"
REL_CLASS_PATH="../java-advanced-2021/artifacts/info.kgeorgiy.java.advanced.implementor.jar"
CLASS_PATH="${ROOT}/${REL_CLASS_PATH}"

function cleanup() {
    cd "${ROOT}"
    rm -Rf "${BUILD_DIR}"
    mv "${PACKAGE}" "java-solutions"
}

function abort() {
    cleanup
    exit 1
}

echo "Collecting sources"

mv "java-solutions" "${PACKAGE}"

SOURCES=$(find "${PACKAGE}/${PACKAGE_PATH}" -type f -name '*.java')
javac -p "${MODULE_PATH}" -d "${BUILD_DIR}" --module-source-path "./" ${SOURCES} || abort

cd "${BUILD_DIR}/${MODULE}"

cat >> MANIFEST.MF <<EOF
Manifest-Version: 1.0
Main-Class: ${PACKAGE}.Implementor
Class-Path: ../${REL_CLASS_PATH}
EOF

echo "Creating jar"
CLASSES=$(find "." -type f -name '*.class')

[ ! -d "${ROOT}/${ARTIFACTS_FOLDER}" ] && mkdir "${ROOT}/${ARTIFACTS_FOLDER}"

# jar -cfe "${ROOT}/${ARTIFACTS_FOLDER}/${MODULE}.jar" "${PACKAGE}.Implementor" ${CLASSES} || abort
jar -cfm "${ROOT}/${ARTIFACTS_FOLDER}/${MODULE}.jar" "MANIFEST.MF" ${CLASSES} || abort

cleanup
# Running: java -p "artifacts/:../java-advanced-2021/artifacts/:../java-advanced-2021/lib/" -m info.kgeorgiy.ja.yaroshevskij.implementor/info.kgeorgiy.ja.yaroshevskij.implementor.Implementor
