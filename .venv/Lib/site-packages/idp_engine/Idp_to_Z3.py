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

Translates AST tree to Z3

TODO: vocabulary

"""
from __future__ import annotations

from copy import copy
from fractions import Fraction
from typing import TYPE_CHECKING
from z3 import (Z3Exception, Datatype, DatatypeRef, ExprRef, Function,
                RecFunction, Const, FreshConst, BoolSort, IntSort, RealSort,
                Or, Not, And, ForAll, Exists, Sum, If, BoolVal, RatVal, IntVal,
                RecAddDefinition)

from .Parse import (TypeDeclaration, SymbolDeclaration, TupleIDP, Ranges,
                    IntRange, RealRange, DateRange)
from .Expression import (catch_error, Constructor, Expression, AIfExpr,
                         Quantee, AQuantification, Operator, Symbol,
                         ADisjunction, AConjunction, AComparison, AUnary,
                         AAggregate, AppliedSymbol, UnappliedSymbol, Number,
                         Date, Brackets, Variable, TRUE, RecDef)
from .utils import (BOOL, INT, REAL, DATE,
                    GOAL_SYMBOL, RELEVANT, RESERVED_SYMBOLS, Semantics)

if TYPE_CHECKING:
    from .Theory import Theory

# class TypeDeclaration  ###########################################################

@catch_error
def translate(self, problem: Theory):
    out = problem.z3.get(self.name, None)
    if out is None:
        if self.name == BOOL:
            out = BoolSort(problem.ctx)
            self.constructors[0].type = BOOL
            self.constructors[1].type = BOOL
            problem.z3[self.constructors[0].name] = BoolVal(True, problem.ctx)
            problem.z3[self.constructors[1].name] = BoolVal(False, problem.ctx)
            self.constructors[0].py_value = True
            self.constructors[1].py_value = False
        elif self.constructors:
            sort = Datatype(self.name, ctx=problem.ctx)
            for c in self.constructors:
                sort.declare(c.name,
                             *[(a.decl.name,
                                a.decl.out.translate(problem) if a.decl.out.name != self.name else
                                sort)  # recursive data type
                               for a in c.sorts])
            out = sort.create()

            for c in self.constructors:
                c.py_value = out.__dict__[c.name]
                problem.z3[c.name] = c.py_value
                if c.tester:
                    problem.z3[c.tester.name] = out.__dict__[f"is_{c.name}"]
                for a in c.sorts:
                    problem.z3[a.decl.name] = out.__dict__[a.accessor.name]
                if not c.sorts:
                    self.map[str(c)] = UnappliedSymbol.construct(c)
                elif c.range:
                    for e in c.range:
                        self.map[str(e)] = e
        elif type(self.interpretation.enumeration) in [Ranges, IntRange, RealRange, DateRange]: # list of numbers
            out = (IntSort(problem.ctx) if self.interpretation.enumeration.type in [INT, DATE] else
                   RealSort(problem.ctx))
        else:  # empty type --> don't care
            out = IntSort(problem.ctx)
        problem.z3[self.name] = out
    return out
TypeDeclaration.translate = translate


# class SymbolDeclaration  ###########################################################

@catch_error
def translate(self, problem: Theory):
    out = problem.z3.get(self.name, None)
    if out is None:
        recursive = any(self in def_.clarks
                        for _, def_ in problem.def_constraints.keys()
                        if def_.mode == Semantics.RECDATA)
        if len(self.sorts) == 0:
            out = Const(self.name, self.out.decl.base_type.translate(problem))
        else:
            types = ( [x.decl.base_type.translate(problem) for x in self.sorts]
                    + [self.out.decl.base_type.translate(problem)])
            out = (Function(self.name, types) if not recursive else
                   RecFunction(self.name, types))
        problem.z3[self.name] = out
    return out
SymbolDeclaration.translate = translate


# class TupleIDP  ###########################################################

@catch_error
def translate(self, problem: Theory):
    return [arg.translate(problem) for arg in self.args]
TupleIDP.translate = translate

# class Constructor  ###########################################################

@catch_error
def translate(self, problem: Theory):
    return problem.z3[self.name]
Constructor.translate = translate


# class Expression  ###########################################################

def translate(self, problem: Theory, vars={}) -> ExprRef:
    """Converts the syntax tree to a Z3 expression, with lookup in problem.z3

    Args:
        problem (Theory): holds the context for the translation (e.g. a cache of translations).

        vars (dict[id, ExprRef], optional): mapping from Variable's id to Z3 translation.
            Filled in by AQuantifier.  Defaults to {}.

    Returns:
        ExprRef: Z3 expression
    """
    out = problem.z3.get(self.str, None)
    if out is None:
        out = self.translate1(problem, vars)
        if not vars:
            problem.z3[self.str] = out
    return out
Expression.translate = translate

def reified(self, problem: Theory) -> DatatypeRef:
    str = b'*' + self.code.encode()
    out = problem.z3.get(str, None)
    if out is None:
        out = Const(str, BoolSort(problem.ctx))
        problem.z3[str] = out
    return out
Expression.reified = reified


# class Symbol  ###############################################################

@catch_error
def translate(self, problem: Theory, vars={}):
    if self.name == BOOL:
        return BoolSort(problem.ctx)
    elif self.name == INT:
        return IntSort(problem.ctx)
    elif self.name == REAL:
        return RealSort(problem.ctx)
    else:
        return self.decl.translate(problem,)
Symbol.translate=translate


# Class AIfExpr  ###############################################################

@catch_error
def translate1(self, problem: Theory, vars={}) -> ExprRef:
    """Converts the syntax tree to a Z3 expression, without lookup in problem.z3

    A lookup is wasteful when `self` is a subformula of a formula that is not in `problem.z3`.

    Args:
        problem (Theory): holds the context for the translation (e.g. a cache of translations).

        vars (dict[id, ExprRef], optional): mapping from Variable's id to Z3 translation.
            Filled in by AQuantifier.  Defaults to {}.

    Returns:
        ExprRef: Z3 expression
    """
    return If(self.sub_exprs[AIfExpr.IF].translate(problem, vars),
              self.sub_exprs[AIfExpr.THEN].translate(problem, vars),
              self.sub_exprs[AIfExpr.ELSE].translate(problem, vars))
AIfExpr.translate1 = translate1


# Class Quantee  ######################################################

@catch_error
def translate(self, problem: Theory, vars={}):
    out = {}
    for vars in self.vars:
        for v in vars:
            translated = FreshConst(v.sort.decl.base_type.translate(problem))
            out[v.str] = translated
    return out
Quantee.translate = translate

# Class AQuantification  ######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    local_vars = {}
    for q in self.quantees:
        local_vars.update(q.translate(problem, vars))
    all_vars = copy(vars)
    all_vars.update(local_vars)
    forms = [f.translate(problem, all_vars) for f in self.sub_exprs]

    if self.q == '∀':
        forms = (And(forms) if 1 < len(forms) else
                 forms[0]   if 1 == len(forms) else
                 BoolVal(True, problem.ctx))
        if local_vars:
            forms = ForAll(list(local_vars.values()), forms)
    else:
        forms = (Or(forms) if 1 < len(forms) else
                 forms[0]  if 1 == len(forms) else
                 BoolVal(False, problem.ctx))
        if local_vars:
            forms = Exists(list(local_vars.values()), forms)
    return forms
AQuantification.translate1 = translate1


# Class Operator  #######################################################

Operator.MAP = {'∧': lambda x, y: And(x, y),
                '∨': lambda x, y: Or(x, y),
                '⇒': lambda x, y: Or(Not(x), y),
                '⇐': lambda x, y: Or(x, Not(y)),
                '⇔': lambda x, y: x == y,
                '+': lambda x, y: x + y,
                '-': lambda x, y: x - y,
                '⨯': lambda x, y: x * y,
                '/': lambda x, y: x / y,
                '%': lambda x, y: x % y,
                '^': lambda x, y: x ** y,
                '=': lambda x, y: x == y,
                '<': lambda x, y: x < y,
                '>': lambda x, y: x > y,
                '≤': lambda x, y: x <= y,
                '≥': lambda x, y: x >= y,
                '≠': lambda x, y: x != y
                }


@catch_error
def translate1(self, problem: Theory, vars={}):
    out = self.sub_exprs[0].translate(problem, vars)

    for i in range(1, len(self.sub_exprs)):
        function = Operator.MAP[self.operator[i - 1]]
        try:
            out = function(out, self.sub_exprs[i].translate(problem, vars))
        except Exception as e:
            raise e
    return out
Operator.translate1 = translate1


# Class ADisjunction  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    if len(self.sub_exprs) == 1:
        out = self.sub_exprs[0].translate(problem, vars)
    else:
        out = Or([e.translate(problem, vars) for e in self.sub_exprs])
    return out
ADisjunction.translate1 = translate1


# Class AConjunction  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    if len(self.sub_exprs) == 1:
        out = self.sub_exprs[0].translate(problem, vars)
    else:
        out = And([e.translate(problem, vars) for e in self.sub_exprs])
    return out
AConjunction.translate1 = translate1


# Class AComparison  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    assert not self.operator == ['≠'],f"Internal error: {self}"
    # chained comparisons -> And()
    out = []
    for i in range(1, len(self.sub_exprs)):
        x = self.sub_exprs[i-1].translate(problem, vars)
        assert x is not None, f"Internal error: {x} is None"
        function = Operator.MAP[self.operator[i - 1]]
        y = self.sub_exprs[i].translate(problem, vars)
        assert y is not None, f"Internal error: {y} is None"
        try:
            out = out + [function(x, y)]
        except Z3Exception as e:
            self.check(False,
                       "{}:{}{}{}".format(str(e),str(x), self.operator[i - 1], str(y)))
    if 1 < len(out):
        return And(out)
    else:
        return out[0]
AComparison.translate1 = translate1


# Class AUnary  #######################################################

AUnary.MAP = {'-': lambda x: 0 - x,
              '¬': lambda x: Not(x)
              }

@catch_error
def translate1(self, problem: Theory, vars={}):
    out = self.sub_exprs[0].translate(problem, vars)
    function = AUnary.MAP[self.operator]
    try:
        return function(out)
    except:
        self.check(False, f"Incorrect syntax {self}")
AUnary.translate1 = translate1


# Class AAggregate  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    assert self.annotated and not self.quantees, f"Cannot expand {self.code}"
    return Sum([f.translate(problem, vars) for f in self.sub_exprs])
AAggregate.translate1 = translate1


# Class AppliedSymbol  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    if self.as_disjunction:
        return self.as_disjunction.translate(problem, vars)
    self.check(self.decl, f"Unknown symbol: {self.symbol}.\n"
               f"Possible fix: introduce a variable "
               f"(e.g., !x in Concept: x=... => $(x)(..))")
    self.check(not self.is_enumerated,
               f"{self.decl.name} is not enumerated")
    self.check(not self.in_enumeration,
               f"Internal error")
    if self.decl.name in [GOAL_SYMBOL, RELEVANT]:
        return TRUE.translate(problem, vars)
    if self.decl.name == 'abs':
        arg = self.sub_exprs[0].translate(problem, vars)
        return If(arg >= 0, arg, -arg, problem.ctx)
    assert self.decl.name not in RESERVED_SYMBOLS, \
               f"Can't resolve argument of built-in symbols: {self}"
    self.check(len(self.sub_exprs) == self.decl.arity,
                f"Incorrect number of arguments for {self}")
    if len(self.sub_exprs) == 0:
        return self.decl.translate(problem)
    else:
        arg = [x.translate(problem, vars) for x in self.sub_exprs]
        # assert  all(a != None for a in arg)
        try:
            return (self.decl.translate(problem))(arg)
        except:
            if self.original.code.startswith('$'):
                msg = f"$()() expression is not properly guarded: {self.original.code}"
            else:
                msg = f"Incorrect symbol application: {self}"
            self.check(False, msg)
AppliedSymbol.translate1 = translate1

def reified(self, problem: Theory, vars={}) -> DatatypeRef:
    if self.is_reified():
        str = b'*'+self.code.encode()
        out = problem.z3.get(str, None)
        if out is None:
            sort = (BoolSort(problem.ctx) if self.in_enumeration or self.is_enumerated else
                    self.decl.out.decl.base_type.translate(problem))
            out = Const(str, sort)
            problem.z3[str] = out
    else:
        out = self.translate(problem)
    return out
AppliedSymbol.reified = reified


# Class UnappliedSymbol  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    return problem.z3[self.name]
UnappliedSymbol.translate1 = translate1


# Class Variable  #######################################################

@catch_error
def translate(self, problem: Theory, vars={}):
    return vars[self.str]
Variable.translate = translate


# Class Number  #######################################################

@catch_error
def translate(self, problem: Theory, vars={}):
    out = problem.z3.get(self.str, None)
    if out is None:
        out = (RatVal(self.py_value.numerator, self.py_value.denominator,
                      problem.ctx)
               if isinstance(self.py_value, Fraction) else
               IntVal(self.py_value, problem.ctx))
        problem.z3[self.str] = out
    return out
Number.translate = translate


# Class Date  #######################################################

@catch_error
def translate(self, problem: Theory, vars={}):
    out = problem.z3.get(self.str, None)
    if out is None:
        out = IntVal(self.py_value, problem.ctx)
        problem.z3[self.str] = self.py_value
    return out
Date.translate = translate


# Class Brackets  #######################################################

def translate1(self, problem: Theory, vars={}):
    return self.sub_exprs[0].translate(problem, vars)
Brackets.translate1 = translate1


# Class RecDef  #######################################################

@catch_error
def translate1(self, problem: Theory, vars={}):
    local_vars = {}
    for v in self.vars:
        translated = FreshConst(v.sort.decl.base_type.translate(problem))
        local_vars[v.str] = translated
    all_vars = copy(vars)
    all_vars.update(local_vars)
    decl = problem.declarations[self.name]
    func = decl.translate(problem)
    # add definition to context
    RecAddDefinition(func, list(local_vars.values()),
                    self.sub_exprs[0].translate(problem, all_vars))
    return TRUE.translate(problem)
RecDef.translate1 = translate1


Done = True
