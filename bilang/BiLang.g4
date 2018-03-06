grammar BiLang;

program : typeDec* block EOF ;

typeDec : 'type' name=ID '=' typeExp ;
typeExp
    : '{' vals+=INT (',' vals+=INT)* '}'  # SubsetTypeExp
    | '{' start=INT '..' end=INT '}'      # RangeTypeExp
    ;

block : stmt+ ;

exp
    : '(' exp ')'                          # ParenExp
    | callee=varRef '(' (args+=exp (',' args+=exp)*)?  ')' # CallExp
    | op=('-' | '!') exp                   # UnOpExp
    | left=exp op=('*' | '/') right=exp    # BinOpMultExp
    | left=exp op=('+' | '-') right=exp    # BinOpAddExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp    # BinOpCompExp
    | left=exp op=('==' | '!=') right=exp  # BinOpEqExp
    | left=exp op=('&&' | '||') right=exp  # BinOpBoolExp
    | INT                                  # NumLiteralExp
    | ADDRESS                              # AddressLiteralExp
    | name=varRef                          # IdExp
    | role=ID '.' field=ID                 # MemberExp
    | 'undefined'                          # UndefExp
    | cond=exp '?' ifTrue=exp ':' ifFalse=exp # IfExp
    ;

stmt
    : 'var' dec=varDec ('=' init=exp)? ';'   # VarDef
    | 'yield' hidden='hidden'? packets ';'          # YieldDef
    | 'join' packetsBind ';'                 # JoinDef
    | 'join' 'many' role=ID ';'              # JoinManyDef

    | target=varRef ':=' exp ';'             # AssignStmt
    | 'reveal' target=varRef where=whereClause';'             # RevealStmt
    | 'if' '(' exp ')' '{' ifTrue=block '}'
       ('else' '{' ifFalse=block '}')?               # IfStmt
    | 'for' 'yield' packetsBind
      'from' from=ID '{' block '}'           # ForYieldStmt
    | 'transfer' target=exp 'from' from=exp 'to' to=exp ';' # TransferStmt
    ;

packetsBind : packets;
packets : packet+ where=whereClause;
whereClause : ('where' cond=exp)? ;
packet : (role=ID ('(' (decls+=varDec (',' decls+=varDec)*)? ')')?) ;

varRef: ID ;

varDec : name=ID ':' type=ID;

// LEXER
ID: [a-zA-Z_][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
