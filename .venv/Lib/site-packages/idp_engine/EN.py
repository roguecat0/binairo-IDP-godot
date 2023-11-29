# Copyright 2019-2023 Ingmar Dasseville, Pierre Carbonnelle
#
# This file is part of IDP-Z3.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

"""

Methods to show a Theory in plain English.

"""
from __future__ import annotations

from copy import copy

from .Parse import IDP
from .Parse import Definition, Rule
from .Expression import (ASTNode, AIfExpr, Quantee, AQuantification,
                         AAggregate, AImplication, ARImplication,
                         Operator, AComparison, AUnary, AppliedSymbol,
                         Brackets)
from .Theory import Theory
from .utils import NEWL


def EN(self):
    out = "\n".join(f'Theory {name}:\n{Theory(th).EN()}\n'
                    for name, th in self.theories.items())
    return out
IDP.EN = EN


def EN(self):
    return str(self)
ASTNode.EN = EN


def EN(self):
    rules = '\n'.join(f"    {r.original.EN()}." for r in self.rules)
    return "Definition:\n" + rules
Definition.EN = EN


def EN(self):
    #TODO len(self.quantees) > self.definiendum.symbol.decl.arity
    vars = ','.join([f"{q}" for q in self.quantees])
    quant = f"for each {','.join(str(q) for q in self.quantees)}, " if vars else ""
    return (f"{quant}"
            f"{self.definiendum.EN()} "
            f"{(' is ' + str(self.out.EN())) if self.out else ''}"
            f" if {str(self.body.EN())}").replace("  ", " ")
Rule.EN = EN


def EN(self):
    return (f"if {self.sub_exprs[AIfExpr.IF  ].EN()}"
            f" then {self.sub_exprs[AIfExpr.THEN].EN()}"
            f" else {self.sub_exprs[AIfExpr.ELSE].EN()}")
AIfExpr.EN = EN


def EN(self):
    signature = ("" if len(self.sub_exprs) <= 1 else
                    f"[{','.join(t.EN() for t in self.sub_exprs[1:-1])}->{self.sub_exprs[-1].EN()}]"
    )
    return (f"{','.join(str(v) for vs in self.vars for v in vs)}"
            f"{f' in {self.sub_exprs[0]}' if self.sub_exprs else ''}"
            f"{signature}")
Quantee.EN = EN


def EN(self):
    self = self.original
    vars = ','.join([f"{q.EN()}" for q in self.quantees])
    if not vars:
        return self.sub_exprs[0].EN()
    elif self.q == '∀':
        return f"for every {vars}, it is true that {self.sub_exprs[0].EN()}"
    elif self.q == '∃':
        return f"there is a {vars} such that {self.sub_exprs[0].EN()}"
    self.check(False, "Internal error")
AQuantification.EN = EN


def EN(self):
    def origine(x):
        return x if x.original == x or not x.annotated else origine(x.original)
    self = origine(self)
    vars = ",".join([f"{q.EN()}" for q in self.quantees])
    if self.aggtype in ['sum', 'min', 'max']:
        return (f"the {self.aggtype} of "
                f"{self.sub_exprs[0].EN()} "
                f"for all {vars}"
                f"{f' such that {self.sub_exprs[1].EN()}' if len(self.sub_exprs) == 2 else ''}")
    else: #  #
        return (f"the number of {vars} such that "
                f"{self.sub_exprs[0].EN()}")
AAggregate.EN = EN


Operator.EN_map =  {'∧': " and ",
                    '∨': " or ",
                    '⇒': " are sufficient conditions for ",
                    '⇐': " are necessary conditions for ",
                    '⇔': " if and only if ",
                    "=": " is ",
                    "≠": " is not ",
                    }

def EN(self):
    def parenthesis(precedence, x):
        return f"({x.EN()})" if type(x).PRECEDENCE <= precedence else f"{x.EN()}"
    precedence = type(self).PRECEDENCE
    temp = parenthesis(precedence, self.sub_exprs[0])
    for i in range(1, len(self.sub_exprs)):
        op = Operator.EN_map.get(self.operator[i-1], self.operator[i-1])
        temp += f" {op} {parenthesis(precedence, self.sub_exprs[i])}"
    return temp
Operator.EN = EN


def EN(self):
    if 2 < len(self.sub_exprs):
        return Operator.EN(self)
    elif type(self.original) == ARImplication:
        return Operator.EN(self.original)
    return f"if {self.sub_exprs[0].EN()}, then {self.sub_exprs[1].EN()}"
AImplication.EN = EN


def EN(self):
    if (type(self.sub_exprs[0]) == AComparison
        and len(self.sub_exprs[0].sub_exprs) == 2
        and self.sub_exprs[0].operator[0] == "="):
        # ~(a=b)
        new_expr = copy(self.sub_exprs[0])
        new_expr.operator[0] = "≠"
        return new_expr.EN()
    op = "not" if self.operator == '¬' else self.operator
    return f"{op}({self.sub_exprs[0].EN()})"
AUnary.EN = EN


def EN(self):
    if self.symbol.decl:
        en = self.symbol.decl.annotations.get('EN', None)
        if en:
            out = en.format("", *(e.EN() for e in self.sub_exprs))
        else:
            out = f"{self.symbol}({', '.join([x.EN() for x in self.sub_exprs])})"
    else:
        out = f"concept {self.symbol.sub_exprs[0]} applied to ({', '.join([x.EN() for x in self.sub_exprs])})"
    if self.in_enumeration:
        enum = f"{', '.join(str(e) for e in self.in_enumeration.tuples)}"
    return (f"{out}"
            f"{ ' '+self.is_enumerated if self.is_enumerated else ''}"
            f"{ f' {self.is_enumeration} {{{enum}}}' if self.in_enumeration else ''}")
AppliedSymbol.EN = EN


def EN(self):
    return f"({self.sub_exprs[0].EN()})"
Brackets.EN = EN


def EN(self) -> str:
    """returns a string containing the Theory in controlled English
    """
    def annot(c):
        return f"[{c.annotations['reading']}]{NEWL}    " if c.annotations['reading'] else ''
    constraints = '\n'.join(f"- {annot(c)}"
                            f"{c.original.EN()}."
                            for c in self.constraints.values()
                            if not c.is_type_constraint_for
                            and (not type(c)==AppliedSymbol or c.symbol.decl.name != "relevant")
                            ).replace("  ", " ")
    definitions = '\n'.join(f"- {d.EN()}" for d in self.definitions)
    return (definitions + ("\n" if definitions else '') + constraints)
Theory.EN = EN


Done = True
