from semanal import make_model
from codegen import print_contract
import ast


def parse_examples(code):
    node = ast.parse(code)
    for defn in node.body:
        if isinstance(defn, ast.AsyncFunctionDef):
            decls, stmts = make_model(defn)
            print_contract(defn.name, decls, stmts)


if __name__ == '__main__':
    with open('examples.py') as f:
        parse_examples(f.read())
