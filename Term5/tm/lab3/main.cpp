#include <cstdlib>
#include <iostream>
#include <string>

#include "calc_driver.hpp"

void print_usage(const char *file, std::ostream &out) {
  out << "Usage: " << file << " [-h] <file>" << std::endl;
  out << "    file  Provide '-' to read from stdin or filename" << std::endl;
  out << "    -h    Print this message" << std::endl;
}

int main(const int argc, const char **argv) {
  if (argc < 2) {
    std::cerr << "Not enough arguments" << std::endl;
    print_usage(argv[0], std::cerr);
    return EXIT_FAILURE;
  }
  int argi = 1;
  Calc::CalcDriver driver;
  if (std::string(argv[argi++]) == "-") {
    driver.parse(std::cin);
  } else {
    driver.parse(argv[1]);
  }

  return EXIT_SUCCESS;
}
