#!/bin/bash

CODE=$(cat task$1.cpp | grep -z "//#.*CODE BEGIN.*CODE END#*" -o | sed "s/\/.*CODE.*//g")
cat > sol.cpp <<EOF
#include "template.cpp"
$CODE
EOF
