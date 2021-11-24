%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token GLOBAL /* global */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT
%token <bool> BOOL
%token TINT     /* int */
%token TBOOL    /* boolean */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token FOR      /* For */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token IOR      /* [|] */
%token IAND     /* [&] */
%token OR       /* | */
%token AND      /* & */
%token NEQ      /* != */
%token EQEQ     /* == */
%token GTE      /* >= */
%token GT       /* > */
%token LTE      /* <= */
%token LT       /* < */
%token SHR      /* >>> */
%token SAR      /* >> */
%token SHL      /* << */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */

%token TRUE /* true */
%token FALSE /* false */
%token NEW /* new */

%left IOR
%left IAND
%left OR
%left AND
%left NEQ
%left EQEQ
%left LTE LT GT GTE SHR SAR SHL
%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TBOOL  { TBool }
  | TINT   { TInt }
  | r=rtyp { TRef r } 

%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | GTE    { Gte }
  | GT     { Gt}
  | LTE    { Lte }
  | LT     { Lt }
  | SAR    { Sar }
  | SHR    { Shr }
  | SHL    { Shl }
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq }
  | NEQ    { Neq }
  | AND    { And }
  | OR     { Or }
  | IAND   { IAnd }
  | IOR    { IOr }

  %inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, gexp) RBRACE
               { loc $startpos $endpos @@ CArr (t, es) }
  | b=BOOL     { loc $startpos $endpos @@ CBool b }
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT      { loc $startpos $endpos @@ CInt i }
  | s = STRING { loc $startpos $endpos @@ CStr(s) }

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | id=IDENT            { loc $startpos $endpos @@ Id id}
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | t=rtyp NULL           { loc $startpos $endpos @@ CNull t }
  | TRUE                  { loc $startpos $endpos @@ CBool true }
  | FALSE                 { loc $startpos $endpos @@ CBool false }
  | s = STRING { loc $startpos $endpos @@ CStr(s) }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e,es) }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }
  | NEW t=ty LBRACKET e=exp RBRACKET
                        { loc $startpos $endpos @@ NewArr(t, e)}
  | LPAREN e=exp RPAREN { e }


vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

vdecls:
  | lst=separated_list(COMMA, vdecl) { lst }

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | FOR LPAREN lst=vdecls SEMI e=option(exp) SEMI s=option(stmt) RPAREN b=block { loc $startpos $endpos @@ For(lst, e, s, b) }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
