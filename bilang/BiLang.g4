grammar BiLang;

program : typeDec* block EOF ;

typeDec : 'type' name=ID '=' typeDef ;
typeDef
    : '{' vals+=INT (',' vals+=INT)* '}'  # SubsetTypeDef
    | '{' start=INT '..' end=INT '}'      # RangeTypeDef
    ;

block : stmt+ ;

exp
    : '(' exp ')'                          # ParenExp
    | callee=ID '(' (args+=exp (',' args+=exp)*)?  ')' # CallExp
    | op=('-' | '!') exp                   # UnOpExp
    | left=exp op=('*' | '/') right=exp    # BinOpMultExp
    | left=exp op=('+' | '-') right=exp    # BinOpAddExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp    # BinOpCompExp
    | left=exp op=('&&' | '||') right=exp  # BinOpBoolExp
    | left=exp op=('==' | '!=') right=exp  # BinOpEqExp
    | INT                                  # NumLiteralExp
    | ADDRESS                              # AddressLiteralExp
    | name=ID                              # IdExp
    | ID '.' ID                            # MemberExp
    | 'undefined'                          # UndefExp
    | cond=exp '?' ifTrue=exp ':' ifFalse=exp # IfExp
    ;

stmt
    : 'var' dec=varDec ('=' init=exp)? ';'  # VarDef
    | 'yield' 'hidden'? packets+=packetDef+ where=whereClause ';'   # YieldDef
    | 'join' 'many'? role=ID where=whereClause ';'      # JoinDef

    | lvalue=ID ':=' exp ';'               # AssignStmt
    | 'reveal' ID ';'                      # RevealStmt
    | 'if' '(' exp ')' '{' block '}'
       ('else' '{' block '}')?             # IfStmt
    | 'for' 'yield' packet=packetDef
      'from' from=ID where=whereClause '{' block '}'  # ForYieldStmt
    | 'transfer' exp 'from' from=exp 'to' to=exp ';' # TransferStmt
    ;

packetDef : (role=exp '(' (decls+=varDec (',' decls+=varDec)*)? ')') ;
whereClause : ('where' exp)? ;
varDec : name=ID ':' type=ID;

// LEXER
ID: [a-zA-Z_][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
