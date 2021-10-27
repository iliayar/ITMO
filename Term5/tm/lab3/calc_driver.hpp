#pragma once
#include <cstddef>
#include <istream>
#include <map>
#include <string>

#include "calc_scanner.hpp"
#include "calc_parser.tab.hh"

namespace Calc {

class CalcDriver {
public:
  CalcDriver() = default;

  virtual ~CalcDriver();

  /**
   * parse - parse from a file
   * @param filename - valid string with input file
   */
  void parse(std::string const &filename);
  /**
   * parse - parse from a c++ input stream
   * @param is - std::istream&, valid input stream
   */
  void parse(std::istream &iss);

  int get_variable(std::string const &ident);
  void set_variable(std::string const &ident, int value);

private:
  void parse_helper(std::istream &stream);

  Calc::CalcParser *parser = nullptr;
  Calc::CalcScanner *scanner = nullptr;
  std::map<std::string, int> m_variables;

  const std::string red = "\033[1;31m";
  const std::string blue = "\033[1;36m";
  const std::string norm = "\033[0m";
};

} // namespace Calc
