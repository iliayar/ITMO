#include <cctype>
#include <fstream>

#include "calc_driver.hpp"
#include "calc_parser.tab.hh"

Calc::CalcDriver::~CalcDriver() {
  delete (scanner);
  scanner = nullptr;
  delete (parser);
  parser = nullptr;
}

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
  // else
  parse_helper(stream);
  return;
}

void Calc::CalcDriver::parse_helper(std::istream &stream) {

  delete (scanner);
  try {
    scanner = new Calc::CalcScanner(&stream);
  } catch (std::bad_alloc &ba) {
    std::cerr << "Failed to allocate scanner: (" << ba.what()
	      << "), exiting!!\n";
    exit(EXIT_FAILURE);
  }

  delete (parser);
  try {
    parser =
	new Calc::CalcParser((*scanner) /* scanner */, (*this) /* driver */);
  } catch (std::bad_alloc &ba) {
    std::cerr << "Failed to allocate parser: (" << ba.what()
	      << "), exiting!!\n";
    exit(EXIT_FAILURE);
  }
  if (parser->parse()) {
    std::cerr << "Parse failed!!\n";
  }
  return;
}

int Calc::CalcDriver::get_variable(std::string const &ident) {
  return m_variables[ident];
}

void Calc::CalcDriver::set_variable(std::string const &ident, int value) {
  m_variables[ident] = value;
  std::cout << ident << " = " << value << std::endl;
}
