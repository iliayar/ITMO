#!/bin/sh

CMD=$1
shift
for arg do
    $CMD -3 $arg ${arg}_2 | diff -u --from-file ${arg}.eta.3 - || exit 1
done
