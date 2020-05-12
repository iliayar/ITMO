#!/bin/bash

./test_min.py > local.in
cat local.in
./test_min
./task && cat local.out
