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
Methods to simplify an expression using a set of assignments.

"""
from __future__ import annotations

from copy import copy
from typing import Optional

from .Assignments import Status, Assignments
from .Expression import (catch_error, Expression, AQuantification, ADisjunction,
                         AConjunction, AppliedSymbol, AComparison, AUnary,
                         Variable, Brackets, TRUE, FALSE)



def _not(truth):
    return FALSE if truth.same_as(TRUE) else TRUE


# class Expression ############################################################

def simplify_with(self: Expression, assignments: Assignments, co_constraints_too=True) -> Expression:
    """ simplify the expression using the assignments """
    simpler, new_e, co_constraint = None, None, None
    if co_constraints_too and self.co_constraint is not None:
        co_constraint = self.co_constraint.simplify_with(assignments, co_constraints_too)
    new_e = [e.simplify_with(assignments, co_constraints_too) for e in self.sub_exprs]
    self = copy(self)._change(sub_exprs=new_e, simpler=simpler, co_constraint=co_constraint)
    # calculate ass.value on the changed expression, as simplified sub
    # expressions may lead to stronger simplifications
    # E.g., P(C()) where P := {0} and C := 0.
    ass = assignments.get(self.str, None)
    if ass and ass.value is not None:
        return ass.value
    return self.simplify1()
Expression.simplify_with = simplify_with


def symbolic_propagate(self,
                       assignments: Assignments,
                       tag: Status,
                       truth: Optional[Expression] = TRUE
                       ):
    """updates assignments with the consequences of `self=truth`.

    The consequences are obtained by symbolic processing (no calls to Z3).

    Args:
        assignments (Assignments):
            The set of assignments to update.

        truth (Expression, optional):
            The truth value of the expression `self`. Defaults to TRUE.
    """
    if self.code in assignments:
        assignments.assert__(self, truth, tag)
    self.propagate1(assignments, tag, truth)
Expression.symbolic_propagate = symbolic_propagate


def propagate1(self, assignments, tag, truth):
    " returns the list of symbolic_propagate of self, ignoring value and simpler "
    return
Expression.propagate1 = propagate1

# @log  # decorator patched in by tests/main.py
@catch_error
def substitute(self, e0, e1, assignments, tag=None):
    """ recursively substitute e0 by e1 in self (e0 is not a Variable)

    if tag is present, updates assignments with symbolic propagation of co-constraints.

    implementation for everything but AppliedSymbol, UnappliedSymbol and
    Fresh_variable
    """
    assert not isinstance(e0, Variable) or isinstance(e1, Variable), \
               f"Internal error in substitute {e0} by {e1}" # should use interpret instead
    assert self.co_constraint is None,  \
               f"Internal error in substitue: {self.co_constraint}" # see AppliedSymbol instead

    # similar code in AppliedSymbol !
    if self.code == e0.code:
        if self.code == e1.code:
            return self  # to avoid infinite loops
        return e1  # e1 is UnappliedSymbol or Number
    else:
        out = self.update_exprs(e.substitute(e0, e1, assignments, tag)
                                for e in self.sub_exprs)
        return out
Expression.substitute = substitute


# class AQuantification  ######################################################

def symbolic_propagate(self, assignments, tag, truth=TRUE):
    if self.code in assignments:
        assignments.assert__(self, truth, tag)
    if not self.quantees:  # expanded, no variables  dead code ?
        if self.q == '∀' and truth.same_as(TRUE):
            AConjunction.symbolic_propagate(self, assignments, tag, truth)
        elif truth.same_as(FALSE):
            ADisjunction.symbolic_propagate(self, assignments, tag, truth)
AQuantification.symbolic_propagate = symbolic_propagate


# class ADisjunction  #########################################################

def propagate1(self, assignments, tag, truth=TRUE):
    if truth.same_as(FALSE):
        for e in self.sub_exprs:
            e.symbolic_propagate(assignments, tag, truth)
ADisjunction.propagate1 = propagate1


# class AConjunction  #########################################################

def propagate1(self, assignments, tag, truth=TRUE):
    if truth.same_as(TRUE):
        for e in self.sub_exprs:
            e.symbolic_propagate(assignments, tag, truth)
AConjunction.propagate1 = propagate1


# class AUnary  ############################################################

def propagate1(self, assignments, tag, truth=TRUE):
    if self.operator == '¬':
        self.sub_exprs[0].symbolic_propagate(assignments, tag, _not(truth))
AUnary.propagate1 = propagate1


# class AppliedSymbol  ############################################################

def propagate1(self, assignments, tag, truth=TRUE):
    if self.as_disjunction:
        self.as_disjunction.symbolic_propagate(assignments, tag, truth)
    Expression.propagate1(self, assignments, tag, truth)
AUnary.propagate1 = propagate1

# @log_calls  # decorator patched in by tests/main.py
@catch_error
def substitute(self, e0, e1, assignments, tag=None):
    """ recursively substitute e0 by e1 in self """

    assert not isinstance(e0, Variable) or isinstance(e1, Variable), \
        f"should use 'interpret instead of 'substitute for {e0}->{e1}"

    new_branch = None
    if self.co_constraint is not None:
        new_branch = self.co_constraint.substitute(e0, e1, assignments, tag)
        if tag is not None:
            new_branch.symbolic_propagate(assignments, tag)

    if self.as_disjunction is not None:
        self.as_disjunction = self.as_disjunction.substitute(e0, e1,        assignments, tag)
        if tag is not None:
            self.as_disjunction.symbolic_propagate(assignments, tag)

    if self.code == e0.code:
        return e1
    else:
        sub_exprs = [e.substitute(e0, e1, assignments, tag)
                     for e in self.sub_exprs]  # no simplification here
        return self._change(sub_exprs=sub_exprs, co_constraint=new_branch)
AppliedSymbol .substitute = substitute


# class AComparison  ##########################################################

def propagate1(self, assignments, tag, truth=TRUE):
    if truth.same_as(TRUE) and len(self.sub_exprs) == 2 and self.operator == ['=']:
        # generates both (x->0) and (x=0->True)
        # generating only one from universals would make the second one
        # a consequence, not a universal
        if (type(self.sub_exprs[0]) == AppliedSymbol
        and self.sub_exprs[1].is_value()):
            assignments.assert__(self.sub_exprs[0], self.sub_exprs[1], tag)
        elif (type(self.sub_exprs[1]) == AppliedSymbol
        and self.sub_exprs[0].is_value()):
            assignments.assert__(self.sub_exprs[1], self.sub_exprs[0], tag)
AComparison.propagate1 = propagate1


# Class Variable  #######################################################

# @log  # decorator patched in by tests/main.py
@catch_error
def substitute(self, e0, e1, assignments, tag=None):
    if self.sort:
        self.sort = self.sort.substitute(e0,e1, assignments, tag)
    return e1 if self.code == e0.code else self
Variable.substitute = substitute


# class Brackets  ############################################################

def symbolic_propagate(self, assignments, tag, truth=TRUE):
    self.sub_exprs[0].symbolic_propagate(assignments, tag, truth)
Brackets.symbolic_propagate = symbolic_propagate


Done = True
