#!/usr/bin/env bash

ROOT="${PWD}/$(dirname $0)/.."
DIR="${PWD}"

cd "${ROOT}"

COMPILE_COMMAND="scripts/create_module.sh"
echo "${COMPILE_COMMAND}"
$COMPILE_COMMAND > /dev/null

CLASS='info.kgeorgiy.java.advanced.implementor.JarImpler'
# COMMAND="java -p \"artifacts/:../java-advanced-2021/artifacts/:../java-advanced-2021/lib/\" -m info.kgeorgiy.ja.yaroshevskij.implementor/info.kgeorgiy.ja.yaroshevskij.implementor.Implementor -jar ${CLASS} artifacts/${CLASS}Impl.jar"
COMMAND="java -jar artifacts/info.kgeorgiy.ja.yaroshevskij.implementor.jar -jar ${CLASS} artifacts/${CLASS}Impl.jar"
echo "${COMMAND}"
$COMMAND
