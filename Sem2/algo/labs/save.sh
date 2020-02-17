#!/bin/bash


cp task.cpp "task$1.cpp"
cat > sol.cpp <<EOF
#include "template.cpp"

//entry
void sol() {

}
EOF
cp template.cpp task.cpp
