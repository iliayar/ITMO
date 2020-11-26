#!/bin/sh

CMD=$1
shift
for arg do
    $CMD -23 $arg ${arg}_2 | diff -u --from-file ${arg}.eta.23 - || exit 1
done
