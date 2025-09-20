#!/usr/bin/env bash

ROOT="${PWD}/$(dirname $0)/.."
DIR="${PWD}"

DOC_FOLDER="javadoc"
CLASS_PATH="${ROOT}/../java-advanced-2021/artifacts/info.kgeorgiy.java.advanced.implementor.jar:${ROOT}/../java-advanced-2021/lib/junit-4.11.jar"

PACKAGE="info.kgeorgiy.ja.yaroshevskij.implementor"
PACKAGE_PATH="$(echo "${PACKAGE}" | tr '.' '/')"

cd "${ROOT}"

echo "Collecting sources"
cd "${ROOT}/java-solutions/"
SOURCES=$(find "${PACKAGE_PATH}/" -type f -name '*.java')
EXTERN_PATH="${ROOT}/../java-advanced-2021/modules/info.kgeorgiy.java.advanced.implementor/info/kgeorgiy/java/advanced/implementor"
SOURCES="${SOURCES} ${EXTERN_PATH=}/JarImpler.java ${EXTERN_PATH}/Impler.java ${EXTERN_PATH}/ImplerException.java"


echo "${SOURCES}"

javadoc -link "https://docs.oracle.com/en/java/javase/11/docs/api/" -private -d "${DIR}/${DOC_FOLDER}" -cp "${CLASS_PATH}" ${SOURCES}
