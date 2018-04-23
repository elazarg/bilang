grammar BiLang;

program : typeDec* ext EOF ;

typeDec : 'type' name=ID '=' typeExp ;
typeExp
    : '{' vals+=INT (',' vals+=INT)* '}'  # SubsetTypeExp
    | '{' start=INT '..' end=INT '}'      # RangeTypeExp
    | name=ID                             # TypeId
    ;

// only sensible combination is independent yield + many
ext : kind=('join'|'yield'| 'reveal'|'many') query+ ';' ext  # ReceiveExt
    | 'let' 'fold' varDec '=' query 'from' from=ID exp ';' ext  # FoldExt
    | 'return' payoff # ExpExt
    ;

query : role=ID ('(' (decls+=varDec (',' decls+=varDec)*)? ')')? ('where' cond=exp)? ;

payoff
    : <assoc=right> cond=exp '?' ifTrue=payoff ':' ifFalse=payoff # IfPayoff
    | 'let' dec=varDec '=' init=exp 'in' body=payoff  # LetPayoff
    | '(' payoff ')'                          # ParenPayoff
    | '{' items+=item+ '}'                    # PayoffExp
    ;

item : (ID '->' exp ';'?) ;

exp
    : '(' exp ')'                             # ParenExp
    | role=ID '.' field=ID                    # MemberExp
    | callee=ID '(' (args+=exp (',' args+=exp)*)?  ')' # CallExp
    | op=('-' | '!') exp                      # UnOpExp
    | left=exp op=('*' | '/') right=exp       # BinOpMultExp
    | left=exp op=('+' | '-') right=exp       # BinOpAddExp
    | exp op=('!='|'==') 'null'                  # UndefExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp    # BinOpCompExp
    | left=exp op=('==' | '!=' | '<->' | '<-!->') right=exp     # BinOpEqExp
    | left=exp op=('&&' | '||') right=exp     # BinOpBoolExp
    | <assoc=right> cond=exp '?' ifTrue=exp ':' ifFalse=exp # IfExp
    | ('true'|'false')                        # BoolLiteralExp
    | name=ID                                 # IdExp
    | INT                                     # NumLiteralExp
    | ADDRESS                                 # AddressLiteralExp
    | 'let!' dec=varDec '=' init=exp 'in' body=exp  # LetExp
    ;


varDec : name=ID ':' hidden='hidden'? type=ID;

// LEXER
ID: [a-zA-Z_][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
