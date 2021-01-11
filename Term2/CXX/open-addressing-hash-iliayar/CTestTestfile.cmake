# CMake generated Testfile for 
# Source directory: /home/iliayar/Documents/CXX/open-addressing-hash-iliayar
# Build directory: /home/iliayar/Documents/CXX/open-addressing-hash-iliayar
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(tests "/home/iliayar/Documents/CXX/open-addressing-hash-iliayar/test/runUnitTests")
set_tests_properties(tests PROPERTIES  _BACKTRACE_TRIPLES "/home/iliayar/Documents/CXX/open-addressing-hash-iliayar/CMakeLists.txt;30;add_test;/home/iliayar/Documents/CXX/open-addressing-hash-iliayar/CMakeLists.txt;0;")
subdirs("googletest")
subdirs("test")
