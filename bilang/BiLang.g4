grammar BiLang;

program : typeDec* block EOF ;

typeDec : 'type' ID '=' '{' INT (',' INT)* '}';

block : stmt+ ;

exp
    : '(' exp ')'                          # ParenExp
    | ('-' | '!') exp                      # UnOpExp
    | left=exp op=('*' | '/') right=exp    # BinOpMultExp
    | left=exp op=('+' | '-') right=exp    # BinOpAddExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp    # BinOpCompExp
    | left=exp op=('&&' | '||') right=exp  # BinOpBoolExp
    | left=exp ('=='|'!=') right=exp       # BinOpEqExp
    | INT                                  # NumLiteral
    | ID                                   # Id
    | ID '.' ID                            # MemberExp
    | 'undefined'                          # UndefExp
    | exp '?' exp ':' exp                  # IfExp
    ;

stmt
    : varDef                               # DecStmt
    | ID ':=' exp ';'                      # AssignStmt
    | 'reveal' ID ';'                      # RevealStmt
    | 'if'    '(' exp ')' '{' block '}' ('else' '{' block '}')? # IfStmt
    | 'for' 'yield' packet 'from' ID where? '{' block '}'  # ForYieldStmt
    | 'transfer' exp 'from' exp 'to' exp ';' # TransferStmt
    ;

varDef
    : 'var' dec=varDec ('=' init=exp)? ';'
    | 'yield' 'hidden'? packet+ where? ';'
    | 'join' 'many'? ID ';'
    ;

packet : (ID '(' (decls+=varDec (',' decls+=varDec)*)? ')') ;
where : 'where' exp ;
varDec : name=ID ':' type=ID  ;

// LEXER
ID: [a-zA-Z_][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
