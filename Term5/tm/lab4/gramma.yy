
%{
use super::driver;
%}

%token END "0"
%token SECTION_SPLIT
%token "String" LITERAL
%token "String" ALIAS
%token "String" BRACKET_CODE
%token "String" PLAIN_CODE
%token "String" PROP
%token "String" IDENT
%token RULE_DIV
%token SEMICOLON
%token COLON

%type "Vec<String>" prop_args
%type "Vec<String>" rule_right_idents
%type "(Vec<String>, Option<String>)" rule_right
%type "Vec<(Vec<String>, Option<String>)>" rule_rights
%type "String" code

%returns "driver::gramma::Gramma"

%%

%{
let mut builder = driver::gramma::GrammaBuilder::new();
%}

doc : section_first SECTION_SPLIT section_second SECTION_SPLIT section_third ;

code : BRACKET_CODE {{ return $$($1); }}
     | PLAIN_CODE {{ return $$($1); }}
     ;

section_first : code props {{ builder.header($1); }}
	      | props
	      ;

section_second : code rules {{ builder.init_code($1); }}
	       | rules
	       ;

section_third : code {{ builder.fin_code($1); }}
	      |
	      ;

props : prop props
      |
      ;

prop : PROP prop_args {{ builder.add_prop($1, $2); }};

prop_args : prop_args code {{
	    	      $1.push($2);
		      return $$($1);
	    }}
	  | prop_args IDENT {{
	    	      $1.push($2);
		      return $$($1);
	    }}
	  | prop_args LITERAL {{
	    	      $1.push($2);
		      return $$($1);
	    }}
	  | prop_args ALIAS {{
	    	      $1.push($2);
		      return $$($1);
	    }}
	  | {{ return $$(Vec::new()); }}
	  ;

rules : rule rules
      |
      ;

rule : IDENT COLON rule_rights SEMICOLON {{ builder.add_rule_with_eval($1, $3); }} ;

rule_right : rule_right_idents code {{ return $$(($1, Some($2))); }}
	   | rule_right_idents {{ return $$(($1, None)); }}
	   ;

rule_right_idents : rule_right_idents IDENT {{
		    $1.push($2);
		    return $$($1);
		  }}
		  | rule_right_idents ALIAS {{
		    $1.push(builder.get_alias($2));
		    return $$($1);
		  }}
		  | {{ return $$(Vec::new()); }}
		  ;

rule_rights : rule_right {{ return $$(vec![$1]); }}
	    | rule_rights RULE_DIV rule_right {{
	      $1.push($3);
	      return $$($1);
	    }}
	    ;

%%

%{
return builder.build();
%}