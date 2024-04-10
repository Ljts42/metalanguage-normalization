{
module Parser where

import Grammar
import Lexer
}

%name      parseExpr Expr
%name      parseLine Line
%tokentype { Token }
%error     { parseError }

%token COMMA  { CommaT }
%token IDENT  { Ident $$ }
%token IMPL   { ImplT }
%token OR     { OrT }
%token AND    { AndT }
%token NOT    { NotT }
%token LEFTP  { LeftP }
%token RIGHTP { RightP }
%token TURN   { TurnT }

%right IMPL
%left OR
%left AND

%%

Line
  : Context TURN Expr     { Line $1 $3 }

Context
  : Context COMMA Expr  { $3 : $1 }
  | Expr                { [$1] }
  | {- empty -}         { [] }

Expr
  : Disj                { $1 }
  | Disj IMPL Expr      { Binary Impl $1 $3 }

Disj
  : Conj                { $1 }
  | Disj OR Conj        { Binary Or $1 $3 }

Conj
  : Term                { $1 }
  | Conj AND Term       { Binary And $1 $3 }

Term
  : NOT Term            { Not $2 }
  | LEFTP Expr RIGHTP   { $2 }
  | IDENT               { Var $1 }

{
parseError = error "Parse error"
}
