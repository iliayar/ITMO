#include <cctype>
#include <fstream>

#include "calc_driver.hpp"
#include "calc_parser.tab.hh"

Calc::CalcDriver::~CalcDriver() {}

void Calc::CalcDriver::parse(std::string const &filename) {
  std::ifstream in_file(filename);
  if (!in_file.good()) {
    exit(EXIT_FAILURE);
  }
  parse_helper(in_file);
  return;
}

void Calc::CalcDriver::parse(std::istream &stream) {
  if (!stream.good() && stream.eof()) {
    return;
  }
  parse_helper(stream);
  return;
}

void Calc::CalcDriver::parse_helper(std::istream &stream) {
  Calc::CalcScanner scanner(&stream);
  Calc::CalcParser parser(scanner, *this);
  if (parser.parse()) {
    std::cerr << "Parse failed!!\n";
  }
  return;
}

int Calc::CalcDriver::get_variable(std::string const &ident) {
  return m_variables[ident];
}

void Calc::CalcDriver::set_variable(std::string const &ident, int value) {
  if (m_variables.find(ident) != m_variables.end()) {
    std::cerr << red << "Can only assign once: " << ident << norm << std::endl;
    return;
  }
  m_variables[ident] = value;
  std::cout << green << ident << " = " << value << norm << std::endl;
}

void Calc::CalcDriver::print_result(int val) {
  std::cout << blue << val << norm << std::endl;
}
