#!/bin/sh

CMD=$1
shift
for arg do
    $CMD -1 $arg ${arg}_2 | diff -u --from-file ${arg}.eta.1 - || exit 1
done
