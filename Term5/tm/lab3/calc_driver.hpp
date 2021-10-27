#pragma once
#include <cstddef>
#include <istream>
#include <map>
#include <string>

#include "calc_parser.tab.hh"
#include "calc_scanner.hpp"

namespace Calc {

class CalcDriver {
public:
  CalcDriver() = default;

  virtual ~CalcDriver();

  void parse(std::string const &filename);
  void parse(std::istream &iss);

  int get_variable(std::string const &ident);
  void set_variable(std::string const &ident, int value);
  void print_result(int);

private:
  void parse_helper(std::istream &stream);

  std::map<std::string, int> m_variables;

  const std::string green = "\033[1;32m";
  const std::string blue = "\033[1;36m";
  const std::string norm = "\033[0m";
};

} // namespace Calc
