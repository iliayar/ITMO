# CMake generated Testfile for 
# Source directory: /home/iliayar/Documents/CXX/inverted-index-iliayar
# Build directory: /home/iliayar/Documents/CXX/inverted-index-iliayar
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(tests "/home/iliayar/Documents/CXX/inverted-index-iliayar/test/runUnitTests")
set_tests_properties(tests PROPERTIES  _BACKTRACE_TRIPLES "/home/iliayar/Documents/CXX/inverted-index-iliayar/CMakeLists.txt;44;add_test;/home/iliayar/Documents/CXX/inverted-index-iliayar/CMakeLists.txt;0;")
subdirs("googletest")
subdirs("test")
