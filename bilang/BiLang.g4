grammar BiLang;

program : typeDec* ext EOF ;

typeDec : 'type' name=ID '=' typeExp ;
typeExp
    : '{' vals+=INT (',' vals+=INT)* '}'  # SubsetTypeExp
    | '{' start=INT '..' end=INT '}'      # RangeTypeExp
    | name=ID                             # TypeId
    ;

exp
    : '(' exp ')'                             # ParenExp
    | callee=ID '(' (args+=exp (',' args+=exp)*)?  ')' # CallExp
    | op=('-' | '!') exp                      # UnOpExp
    | left=exp op=('*' | '/') right=exp       # BinOpMultExp
    | left=exp op=('+' | '-') right=exp       # BinOpAddExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp    # BinOpCompExp
    | left=exp op=('==' | '!=') right=exp     # BinOpEqExp
    | left=exp op=('&&' | '||') right=exp     # BinOpBoolExp
    | role=ID '.' field=ID                    # MemberExp
    | cond=exp '?' ifTrue=exp ':' ifFalse=exp # IfExp
    | BOOL                                    # BoolLiteralExp
    | name=ID                                 # IdExp
    | INT                                     # NumLiteralExp
    | ADDRESS                                 # AddressLiteralExp
    | 'undefined'                             # UndefExp
    | 'let' dec=varDec '=' init=exp 'in' ext';'    # VarDef
    ;

ext : 'receive' hidden='hidden'? packet+ '->' ext ';'  # YieldDef
    | 'let' 'fold' varDec '=' packet 'from' from=ID exp 'in' ext      # Fold
    | '{' items+=item+ '}'                             # Transfer
    ;

item : (ID '->' exp ';'?) ;

packet : kind=('join'|'yield'|'reveal'|'many') (role=ID ('(' (decls+=varDec (',' decls+=varDec)*)? ')')?) whereClause ;

whereClause : ('where' cond=exp)? ;

varDec : name=ID ':' type=ID;

// LEXER
ID: [a-zA-Z_][a-zA-Z_0-9]*;
BOOL: 'true'|'false';
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
