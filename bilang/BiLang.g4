grammar BiLang;

program : typeDec* ext EOF ;

typeDec : 'type' name=ID '=' typeExp ;
typeExp
    : '{' vals+=INT (',' vals+=INT)* '}'  # SubsetTypeExp
    | '{' start=INT '..' end=INT '}'      # RangeTypeExp
    | name=ID                             # TypeId
    ;

ext : query+ ';' ext  # ReceiveExt
    | 'let' 'fold' varDec '=' query 'from' from=ID exp ';' ext  # FoldExt
    | 'return' exp # ExpExt
    ;

query : kind=('join'|'yield'|'reveal'|'many') (role=ID ('(' (decls+=varDec (',' decls+=varDec)*)? ')')?) whereClause ;

whereClause : ('where' cond=exp)? ;

exp
    : '(' exp ')'                             # ParenExp
    | role=ID '.' field=ID                    # MemberExp
    | callee=ID '(' (args+=exp (',' args+=exp)*)?  ')' # CallExp
    | op=('-' | '!') exp                      # UnOpExp
    | left=exp op=('*' | '/') right=exp       # BinOpMultExp
    | left=exp op=('+' | '-') right=exp       # BinOpAddExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp    # BinOpCompExp
    | left=exp op=('==' | '!=') right=exp     # BinOpEqExp
    | left=exp op=('&&' | '||') right=exp     # BinOpBoolExp
    | <assoc=right> cond=exp '?' ifTrue=exp ':' ifFalse=exp # IfExp
    | '{' items+=item+ '}'                    # PayoffExp
    | ('true'|'false')                        # BoolLiteralExp
    | name=ID                                 # IdExp
    | INT                                     # NumLiteralExp
    | ADDRESS                                 # AddressLiteralExp
    | 'undefined'                             # UndefExp
    | 'let' dec=varDec '=' init=exp 'in' body=exp  # LetExp
    ;

item : (ID '->' exp ';'?) ;

varDec : name=ID ':' hidden='hidden'? type=ID;

// LEXER
ID: [a-zA-Z_][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
