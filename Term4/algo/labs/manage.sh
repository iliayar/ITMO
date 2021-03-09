#!/usr/bin/env bash

CMD="$1"

case $CMD in
    save)
	cp task.cpp "task$2.cpp"
	cat > sol.cpp <<EOF
#include "template.cpp"

//entry
void sol() {

}
EOF
	;;
    load)
	CODE=$(cat task$2.cpp | grep -z "//#.*CODE BEGIN.*CODE END#*" -o | sed "s/\/.*CODE.*//g")
	cat > sol.cpp <<EOF
#include "template.cpp"
$CODE
EOF
	;;
    reset)
	./manage.sh save _tmp
	rm task_tmp.cpp
	;;
    complete)
	mkdir "lab$2"
	mv task?.cpp "lab$2/"
	;;
    *)
	echo "Unknown command"
	;;
esac
