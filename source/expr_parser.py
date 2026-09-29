from lark import Lark, tree, Token, Visitor
from typeguard import typechecked


expr_grammar = r"""
    !expr: wire
        | concatexpr
        | uexpr
        | binexpr
        | parenexpr
        | (whitespace)? expr (whitespace)?
    !parenexpr:   "("  expr  ")"
    !uexpr: uop expr
    !binexpr: expr binop expr
    !concatexpr: "{"  expr ("," expr)+ "}"
    !uop: "!" | "~"
    !binop: "+" | "-" | "*" | "%"
        | "&&" | "||" | "==" | "!==" | "!="
    !wire: var
        | escapedvar 
        | value
        | var (whitespace)? "[" (whitespace)? NUMBER (whitespace)? "]"
        | escapedvar whitespace  "[" (whitespace)? NUMBER (whitespace)? "]"
        | var (whitespace)? "[" (whitespace)? NUMBER (whitespace)? ":" (whitespace)? NUMBER (whitespace)? "]"
        | escapedvar whitespace  "[" (whitespace)? NUMBER (whitespace)? ":" (whitespace)? NUMBER (whitespace)? "]"
        | "`" NAME
    !var: NAME
    !escapedvar: "\\" (NAME | NUMBER | "\\" | "{" | "}" | "." | "$" | "[" | "]")*
    !value: NUMBER
        | NUMBER "'b" ("0"|"1")+
        | NUMBER "'d" HEXDIGIT+
        | NUMBER "'h" HEXDIGIT+     
    !whitespace: (WS | WS_INLINE)+
    %import common.CNAME -> NAME
    %import common.NUMBER
    %import common.HEXDIGIT
    %import common.WS_INLINE
    %import common.WS
 """

parser = Lark(expr_grammar, start='expr', ambiguity='resolve') # ambiguity='explicit' blows up expansion


@typechecked
def collectVars(expr: str) -> set[str]:
    varsSet = set()
    tree = parser.parse(expr)
    for varNode in tree.find_data("var"):
        varName = ""
        for child in varNode.children:
            varName += child.value
        varsSet.add(varName)
    for varNode in tree.find_data("escapedvar"):
        varName = ""
        for child in varNode.children:
            varName += child.value
        varsSet.add(varName)
    return varsSet
