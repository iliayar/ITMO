#pragma once
#if !defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

#include "calc_parser.tab.hh"

namespace Calc {

class CalcScanner : public yyFlexLexer {
public:
  CalcScanner(std::istream *in) : yyFlexLexer(in){};
  virtual ~CalcScanner(){};

  using FlexLexer::yylex;

  virtual int yylex(Calc::CalcParser::semantic_type *const lval,
		    Calc::CalcParser::location_type *location);

private:
  /* yyval ptr */
  Calc::CalcParser::semantic_type *yylval = nullptr;
};

} // namespace Calc
