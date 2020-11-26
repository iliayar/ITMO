#!/bin/sh

CMD=$1
shift
for arg do
    $CMD -123 $arg ${arg}_2 | diff -u --from-file ${arg}.eta.123 - || exit 1
done
