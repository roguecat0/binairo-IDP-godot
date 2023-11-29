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

Methods to simplify a logic expression.

This module monkey-patches the Expression class and sub-classes.


"""
from __future__ import annotations

from copy import copy, deepcopy
import sys
from typing import List, Tuple, Optional, Generator

from .Expression import (Constructor, Expression, AIfExpr, IF,
                         AQuantification, Operator, AEquivalence, AImplication,
                         ADisjunction, AConjunction, AComparison, EQUALS,
                         ASumMinus, AMultDiv, APower, AUnary, AAggregate,
                         SymbolExpr, AppliedSymbol, UnappliedSymbol, Variable,
                         Number, Date, Brackets, TRUE, FALSE, NOT, AND, OR)
from .Parse import Symbol, Enumeration, TupleIDP
from .Assignments import Status as S, Assignment
from .utils import BOOL, INT, DATE, ABS


# class Expression  ###########################################################

def _change(self: Expression,
            sub_exprs: Optional[List[Expression]] = None,
            ops : Optional[List[str]] = None,
            value : Optional[Expression] = None,
            simpler : Optional[Expression] = None,
            co_constraint : Optional[Expression] = None
            ) -> Expression:
    " change attributes of an expression, and resets derived attributes "

    if value:
        out = copy(value)
        out.annotations = self.annotations
        return out

    if simpler is not None:
        simpler.original = self.original
        simpler.is_type_constraint_for = self.is_type_constraint_for
        if type(self) == AppliedSymbol:
            simpler.in_head = self.in_head
        return simpler

    if sub_exprs is not None:
        self.sub_exprs = sub_exprs
    if ops is not None:
        self.operator = ops
    if co_constraint is not None:
        self.co_constraint = co_constraint

    # reset derived attributes
    self.str = sys.intern(str(self))

    return self
Expression._change = _change


def update_exprs(self: Expression,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    """ change sub_exprs and simplify, while keeping relevant info. """
    #  default implementation, without simplification
    return self._change(sub_exprs=list(new_exprs))
Expression.update_exprs = update_exprs


def simplify1(self: Expression) -> Expression:
    return self.update_exprs(self.sub_exprs)
Expression.simplify1 = simplify1



# Class AIfExpr  ###############################################################

def update_exprs(self: AIfExpr,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    sub_exprs = list(new_exprs)
    if_, then_, else_ = sub_exprs[0], sub_exprs[1], sub_exprs[2]
    if if_.same_as(TRUE):
        return self._change(simpler=then_, sub_exprs=sub_exprs)
    elif if_.same_as(FALSE):
        return self._change(simpler=else_, sub_exprs=sub_exprs)
    else:
        if then_.same_as(else_):
            return self._change(simpler=then_, sub_exprs=sub_exprs)
        elif then_.same_as(TRUE):
            if else_.same_as(FALSE):
                return self._change(simpler=if_, sub_exprs=sub_exprs)
            else:
                return self._change(simpler=OR([if_, else_]), sub_exprs=sub_exprs)
        elif else_.same_as(TRUE):
            if then_.same_as(FALSE):
                return self._change(simpler=NOT(if_), sub_exprs=sub_exprs)
            else:
                return self._change(simpler=OR([NOT(if_), then_]), sub_exprs=sub_exprs)
    return self._change(sub_exprs=sub_exprs)
AIfExpr.update_exprs = update_exprs


# Class Quantee  #######################################################


# Class AQuantification  ######################################################

def update_exprs(self: AQuantification,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    if self.q == '∀':
        return AConjunction.update_exprs(self, new_exprs, replace=False)
    else:
        return ADisjunction.update_exprs(self, new_exprs, replace=False)
AQuantification.update_exprs = update_exprs


# Class AImplication  #######################################################

def update_exprs(self: AImplication,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    if type(new_exprs) == list:
        new_exprs = iter(new_exprs)
    exprs0 = next(new_exprs)
    simpler = None
    if exprs0.same_as(FALSE):  # (false => p) is true
        return self._change(value=TRUE)
    elif exprs0.same_as(TRUE):  # (true => p) is p
        exprs1 = next(new_exprs)
        simpler = exprs1
    else:
        exprs1 = next(new_exprs)
        if exprs1.same_as(TRUE):  # (p => true) is true
            return self._change(value=TRUE)
        elif exprs1.same_as(FALSE):  # (p => false) is ~p
            simpler = NOT(exprs0)
        elif exprs1.same_as(exprs0):  # (p => p) is true
            return self._change(value=TRUE)
    return self._change(simpler=simpler,
                        sub_exprs=[exprs0, exprs1])
AImplication.update_exprs = update_exprs


# Class AEquivalence  #######################################################

def update_exprs(self: AEquivalence,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    exprs = list(new_exprs)
    if len(exprs) == 1:
        return self._change(simpler=exprs[1], sub_exprs=exprs)
    for e in exprs:
        if e.same_as(TRUE):  # they must all be true
            return self._change(simpler=AND(exprs),
                                sub_exprs=exprs)
        if e.same_as(FALSE):  # they must all be false
            return self._change(simpler=AND([NOT(e) for e in exprs]),
                                sub_exprs=exprs)
    return self._change(sub_exprs=exprs)
AEquivalence.update_exprs = update_exprs


# Class ADisjunction  #######################################################

def update_exprs(self: Expression,
                 new_exprs: Generator[Expression, None, None],
                 replace=True
                 ) -> Expression:
    exprs = []
    simpler = None
    for expr in new_exprs:
        if expr.same_as(TRUE):
            return self._change(value=TRUE)
        if not expr.same_as(FALSE):
            exprs.append(expr)

    if len(exprs) == 0:  # all disjuncts are False
        return self._change(value=FALSE)
    elif replace and len(exprs) == 1:
        simpler = exprs[0]
    return self._change(simpler=simpler, sub_exprs=exprs)
ADisjunction.update_exprs = update_exprs


# Class AConjunction  #######################################################

# same as ADisjunction, with TRUE and FALSE swapped
def update_exprs(self: Expression,
                 new_exprs: Generator[Expression, None, None],
                 replace=True
                 ) -> Expression:
    exprs = []
    simpler = None
    for expr in new_exprs:
        if expr.same_as(FALSE):
            return self._change(value=FALSE)
        if not expr.same_as(TRUE):
            exprs.append(expr)

    if len(exprs) == 0:  # all conjuncts are True
        return self._change(value=TRUE)
    if replace and len(exprs) == 1:
        simpler = exprs[0]
    return self._change(simpler=simpler, sub_exprs=exprs)
AConjunction.update_exprs = update_exprs


# Class AComparison  #######################################################

def update_exprs(self: AComparison,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    operands = list(new_exprs)

    if len(operands) == 2 and self.operator == ["="]:
        # a = a
        if operands[0].same_as(operands[1]):
            return self._change(value=TRUE)

        # (if c then a else b) = d  ->  (if c then a=d else b=d)
        if type(operands[0]) == AIfExpr:
            then = EQUALS([operands[0].sub_exprs[1], operands[1]]).simplify1()
            else_ = EQUALS([operands[0].sub_exprs[2], operands[1]]).simplify1()
            new = IF(operands[0].sub_exprs[0], then, else_).simplify1()
            return self._change(simpler=new, sub_exprs=operands)

    acc = operands[0]
    assert len(self.operator) == len(operands[1:]), "Internal error"
    for op, expr in zip(self.operator, operands[1:]):
        if acc.is_value() and expr.is_value():
            if op in ["<", ">"] and acc.same_as(expr):
                return self._change(value=FALSE)
            if op == "=" and not acc.same_as(expr):
                return self._change(value=FALSE)
            if op == "≠":  # issue #246
                if acc.same_as(expr):
                    return self._change(value=FALSE)
            elif not (Operator.MAP[op]) (acc.py_value, expr.py_value):
                return self._change(value=FALSE)
        acc = expr
    if all(e.is_value() for e in operands):
        return self._change(value=TRUE)
    return self._change(sub_exprs=operands)
AComparison.update_exprs = update_exprs

def as_set_condition(self: AComparison) -> Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]:
    return ((None, None, None) if not self.is_assignment() else
            (self.sub_exprs[0], True,
             Enumeration(tuples=[TupleIDP(args=[self.sub_exprs[1]])])))
AComparison.as_set_condition = as_set_condition

#############################################################

def update_arith(self: Expression, operands: List[Expression]) -> Expression:
    operands = list(operands)
    if all(e.is_value() for e in operands):
        self.check(all(hasattr(e, 'py_value') for e in operands),
                f"Incorrect numeric type in {self}")
        out = operands[0].py_value

        assert len(self.operator) == len(operands[1:]), "Internal error"
        for op, e in zip(self.operator, operands[1:]):
            function = Operator.MAP[op]

            if op == '/' and self.type == INT:  # integer division
                out //= e.py_value
            else:
                out = function(out, e.py_value)
        value = (Number(number=str(out)) if operands[0].type != DATE else
                 Date.make(out))
        return value
    return self._change(sub_exprs=operands)


# Class ASumMinus  #######################################################

def update_exprs(self: ASumMinus,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    return update_arith(self, new_exprs)
ASumMinus.update_exprs = update_exprs


# Class AMultDiv  #######################################################

def update_exprs(self: AMultDiv,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    operands = list(new_exprs)
    if any(op == '%' for op in self.operator):  # special case !
        if len(operands) == 2 and all(e.is_value() for e in operands):
            out = operands[0].py_value % operands[1].py_value
            return Number(number=str(out))
        else:
            return self._change(sub_exprs=operands)
    return update_arith(self, operands)
AMultDiv.update_exprs = update_exprs


# Class APower  #######################################################

def update_exprs(self: APower,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    operands = list(new_exprs)
    if len(operands) == 2 \
       and all(e.is_value() for e in operands):
        out = operands[0].py_value ** operands[1].py_value
        return Number(number=str(out))
    else:
        return self._change(sub_exprs=operands)
APower.update_exprs = update_exprs


# Class AUnary  #######################################################

def update_exprs(self: AUnary,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    operand = list(new_exprs)[0]
    if self.operator == '¬':
        if operand.same_as(TRUE):
            return self._change(value=FALSE)
        if operand.same_as(FALSE):
            return self._change(value=TRUE)
    else:  # '-'
        if operand.is_value() and type(operand) == Number:
            return Number(number=f"{-operand.py_value}")
    return self._change(sub_exprs=[operand])
AUnary.update_exprs = update_exprs

def as_set_condition(self: AUnary) -> Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]:
    (x, y, z) = self.sub_exprs[0].as_set_condition()
    return ((None, None, None) if x is None else
            (x, not y, z))
AUnary.as_set_condition = as_set_condition


# Class AAggregate  #######################################################

def update_exprs(self: AAggregate,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    operands = list(new_exprs)
    if self.annotated and not self.quantees:
        if all(e.is_value() for e in operands):
            out = sum(e.py_value for e in operands)
            return Number(number=str(out))
    return self._change(sub_exprs=operands)
AAggregate.update_exprs = update_exprs


# Class AppliedSymbol  #######################################################

def update_exprs(self: AppliedSymbol,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    new_exprs = list(new_exprs)
    if not self.decl and type(self.symbol) == Symbol:
        self.decl = self.symbol.decl
    self.type = (BOOL if self.is_enumerated or self.in_enumeration else
            self.decl.type if self.decl else None)
    if self.decl and type(self.decl) == Constructor:
        if all(e.is_value() for e in new_exprs):
            return self._change(sub_exprs=new_exprs)

    # simplify abs()
    if (self.decl and self.decl.name == ABS and len(new_exprs) == 1
        and new_exprs[0].is_value()):
        return Number(number=str(abs(new_exprs[0].py_value)))

    # simplify x(pos(0,0)) to 0,  is_pos(pos(0,0)) to True
    if (len(new_exprs) == 1
        and hasattr(new_exprs[0], 'decl')
        and type(new_exprs[0].decl) == Constructor
        and new_exprs[0].decl.tester
        and self.decl):
        if self.decl.name in new_exprs[0].decl.parent.accessors:
            i = new_exprs[0].decl.parent.accessors[self.decl.name]
            self.check(i < len(new_exprs[0].sub_exprs),
                       f"Incorrect expression: {self}")
            return self._change(simpler=new_exprs[0].sub_exprs[i], sub_exprs=new_exprs)
        if self.decl.name == new_exprs[0].decl.tester.name:
            return self._change(value=TRUE)

    return self._change(sub_exprs=new_exprs)
AppliedSymbol.update_exprs = update_exprs

def as_set_condition(self: AppliedSymbol) -> Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]:
    # determine core after substitutions
    core = AppliedSymbol.make(self.symbol, deepcopy(self.sub_exprs))

    return ((None, None, None) if not self.in_enumeration else
            (core, 'not' not in self.is_enumeration, self.in_enumeration))
AppliedSymbol.as_set_condition = as_set_condition


# Class SymbolExpr  #######################################################

def update_exprs(self: SymbolExpr,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    symbol = list(new_exprs)[0]
    value = (symbol if self.eval == '' else
             symbol.decl.symbol if type(symbol) == UnappliedSymbol and symbol.decl else
             None)
    if value is not None:
        self.check(type(value) != Variable,
                f"Variable `{value}` cannot be applied to argument(s).")
        return value
    return self._change(sub_exprs=[symbol])
SymbolExpr.update_exprs = update_exprs


# Class Brackets  #######################################################

def update_exprs(self: Brackets,
                 new_exprs: Generator[Expression, None, None]
                 ) -> Expression:
    return list(new_exprs)[0]
Brackets.update_exprs = update_exprs


# set conditions  #######################################################

def join_set_conditions(assignments: List[Assignment]) -> List[Assignment]:
    """In a list of assignments, merge assignments that are set-conditions on the same term.

    An equality and a membership predicate (`in` operator) are both set-conditions.

    Args:
        assignments (List[Assignment]): the list of assignments to make more compact

    Returns:
        List[Assignment]: the compacted list of assignments
    """
    #
    for i, c in enumerate(assignments):
        (x, belongs, y) = c.as_set_condition()
        if x:
            for j in range(i):
                (x1, belongs1, y1) = assignments[j].as_set_condition()
                if x1 and x.same_as(x1):
                    if belongs and belongs1:
                        new_tuples = (y.tuples & y1.tuples) # intersect
                    elif belongs and not belongs1:
                        new_tuples = (y.tuples ^ y1.tuples) # difference
                    elif not belongs and belongs1:
                        belongs = belongs1
                        new_tuples = (y1.tuples ^ y.tuples)
                    else:
                        new_tuples = y.tuples | y1.tuples # union
                    # sort again
                    new_tuples = list(new_tuples.values())

                    out = AppliedSymbol.make(
                        symbol=x.symbol, args=x.sub_exprs,
                        is_enumeration='in',
                        in_enumeration=Enumeration(tuples=new_tuples)
                    )

                    core = deepcopy(AppliedSymbol.make(out.symbol, out.sub_exprs))
                    out.as_disjunction = out.in_enumeration.contains([core], False)

                    out = Assignment(out,
                                     TRUE if belongs else FALSE,
                                     S.UNKNOWN)

                    assignments[j] = out # keep the first one
                    assignments[i] = Assignment(TRUE, TRUE, S.UNKNOWN)
    return [c for c in assignments if c.sentence != TRUE]

Done = True
