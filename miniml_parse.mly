/*
                         CS 51 Final Project
                           MiniML -- Parser
*/

%{
  open Printf ;;
  open Expr ;;
%}

%token EOF
%token OPEN CLOSE
%token LET DOT IN REC
%token NEG
%token PLUS MINUS
%token PLUSF MINUSF
%token TIMES
%token TIMESF
%token LESSTHAN EQUALS
%token IF THEN ELSE
%token FUNCTION
%token RAISE
%token TRY
%token WITH
%token <string> EXCN
%token <string> MATCH_CASE
%token <string> ID
%token <int> INT
%token <float> FLOAT
%token TRUE FALSE
%token RAISEEXN
%nonassoc LESSTHAN
%nonassoc EQUALS
%left PLUS MINUS
%left TIMES
%left


%start input
%type <Expr.expr> input

/* Grammar follows */
%%
input:  exp EOF                 { $1 }

exp:    exp expnoapp            { App($1, $2) }
        | expnoapp              { $1 }

expnoapp: INT                   { Num $1 }
        | FLOAT                 { Float $1 }
        | TRUE                  { Bool true }
        | FALSE                 { Bool false }
        | ID                    { Var $1 }
        | exp PLUS exp          { Binop(Plus, $1, $3) }
        | exp MINUS exp         { Binop(Minus, $1, $3) }
        | exp TIMES exp         { Binop(Times, $1, $3) }
        | exp EQUALS exp        { Binop(Equals, $1, $3) }
        | exp LESSTHAN exp      { Binop(LessThan, $1, $3) }
        | exp PLUSF exp         { Binop(Plusf, $1, $3)}
        | exp MINUSF exp        { Binop(Minusf, $1, $3) }
        | exp TIMESF exp        { Binop(Timesf, $1, $3) }
        | NEG exp               { Unop(Negate, $2) }
        | IF exp THEN exp ELSE exp      { Conditional($2, $4, $6) }
        | LET ID EQUALS exp IN exp      { Let($2, $4, $6) }
        | LET REC ID EQUALS exp IN exp  { Letrec($3, $5, $7) }
        | FUNCTION ID DOT exp   { Fun($2, $4) }
        | RAISE                 { Raise }
        | RAISEEXN EXCN           { RaiseExn $2}
        | TRY exp WITH exp       { Trywith($2, $4) }
        | OPEN exp CLOSE        { $2 }
;

%%
