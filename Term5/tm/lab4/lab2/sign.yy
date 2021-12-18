
%{

    use super::{Tree, NodeValue};

%}

%token END "0"
%token ASTERISK
%token COMMA
%token LPAREN
%token RPAREN
%token SEMICOLON
%token "String" IDENTIFIER

%returns "Tree"

%type "Tree" declaration
%type "Tree" args
%type "Tree" args_rest
%type "Tree" arg
%type "Tree" pointer

%%

%{
let mut res: Option<Tree> = None;
%}

inp : declaration {{ res = Some($1); }};

declaration : IDENTIFIER pointer IDENTIFIER LPAREN args RPAREN SEMICOLON
		{{
		    return $$(Tree::new(NodeValue::NonTerminal("DECLARATION".to_string()), vec![
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER($1))),
					    $2,
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER($3))),
					    Tree::node(NodeValue::Terminal(super::Token::LPAREN)),
					    $5,
					    Tree::node(NodeValue::Terminal(super::Token::RPAREN)),
					    Tree::node(NodeValue::Terminal(super::Token::SEMICOLON)),
                                            ]))
                }};

args : arg args_rest
     {{
         return $$(Tree::new(NodeValue::NonTerminal("ARGS".to_string()), vec![ $1, $2 ]));
     }}
     | {{ return $$(Tree::node(NodeValue::NonTerminal("ARGS".to_string()))); }}
     ;	

args_rest : COMMA arg args_rest
          {{
              return $$(Tree::new(NodeValue::NonTerminal("ARGS_REST".to_string()), vec![
                                  Tree::node(NodeValue::Terminal(super::Token::COMMA)),
				  $2,
				  $3,
                                  ]));
          }}
          | {{ return $$(Tree::node(NodeValue::NonTerminal("ARGS_REST".to_string()))); }}
          ;

arg : IDENTIFIER pointer IDENTIFIER
    {{
        return $$(Tree::new(NodeValue::NonTerminal("ARG".to_string()), vec! [
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER($1))),
					    $2,
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER($3))),
                                                  ]))
    }}
    ;

pointer : ASTERISK pointer {{ return $$(Tree::new(NodeValue::NonTerminal("POINTER".to_string()), vec![
					    Tree::node(NodeValue::Terminal(super::Token::ASTERISK)),
					    $2,
                                       ]))}}
	| {{ return $$(Tree::node(NodeValue::NonTerminal("ASTERISK".to_string()))); }}
        ;

%%

%{

    return res.unwrap();

%}
