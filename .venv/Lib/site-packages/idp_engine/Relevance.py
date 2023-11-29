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
This module contains the logic for the computation of relevance.
"""
from __future__ import annotations
from copy import copy

from .Assignments import Status as S
from .Expression import (AppliedSymbol, Expression, AQuantification,
                         AConjunction, Brackets)
from .Theory import Theory
from .utils import OrderedSet, RELEVANT


def split_constraints(constraints: OrderedSet) -> OrderedSet:
    """replace [.., a ∧ b, ..] by [.., a, b, ..]

    This is to avoid dependencies between a and b (see issue #95).

    Args:
        constraints (OrderedSet): set of constraints that may contain conjunctions

    Returns:
        OrderedSet: set of constraints without top-level conjunctions
    """

    def split(c: Expression, cs: OrderedSet):
        """split constraint c and adds it to cs"""
        if type(c) in [AConjunction, Brackets]:
            for e in c.sub_exprs:
                split(e, cs)
        elif type(c) == AQuantification and c.q == '∀':
            conj = OrderedSet()
            for e in c.sub_exprs:
                split(e, conj)
            for e in conj:
                out = AQuantification.make(c.q, c.quantees, e)
                # out.code = c.code
                out.annotations = c.annotations
                cs.append(out)
        else:
            cs.append(c)

    new_constraints = OrderedSet()
    for c in constraints:
        split(c, new_constraints)
    return new_constraints


def determine_relevance(self: Theory) -> Theory:
    """Determines the questions that are relevant in a consistent state of Theory ``self``.

    Some definitions:
    * a consistent state s of theory T is a partial interpretation of vocabulary V of T that can be expanded in a model of T;
    * a solution S of theory T is a state such that every expansion of solution S is a model of theory T;
    * a minimal solution for theory T in state s is a solution that expands state s and is not more precise than another solution of theory T;
    * a symbol is relevant for theory T in state s iff it is interpreted in a minimal solution for theory T in state s.

    This method must be called after a call to ``propagate``, on a Theory created with ``extended=True``.
    The method 1) computes a simplified theory equivalent to ``self``,
    2) collects the relevant questions in that theory. A question is considered relevant if:
    * it appears in a constraint;
    * or it is a goal symbol;
    * or it appears in a co_constraint for a relevant question.

    The result is found in the ``relevant`` attribute of the assignments in ``self.assignments``.

    Returns:
        Theory: the Theory with relevant information in ``self.assignments``.
    """

    assert self.extended == True,\
        "The theory must be created with 'extended=True' for relevance computations."

    # set given information to relevant
    for q in self.assignments.values():
        q.relevant = (q.status in [S.GIVEN, S.DEFAULT, S.EXPANDED])

    # determine goals
    goals = OrderedSet()
    for constraint in self.constraints:  # not simplified
        if (type(constraint) == AppliedSymbol
           and constraint.decl.name == RELEVANT):
            goals.extend(constraint.sub_exprs)  # all instances of the goal symbol

    # simplify for relevance (do not simplify co_constraints, exclude numeric expressions)
    out = self.simplify(for_relevance=True)  # creates a copy

    # collect constraints in the simplified theory (except type constraints)
    constraints = OrderedSet(c for c in out.constraints
                             if c.is_type_constraint_for is None)
    constraints = split_constraints(constraints)
    # also add the propagated assignments used for simplifications  #252, #277
    constraints.extend(q.sentence for q in out.assignments.values()  # out => exclude numeric expressions
                       if q.value is not None)

    # determine the set of relevant questions in constraints
    _relevant = copy(constraints)  # a set of questions and constraints
    _relevant.extend(goals)

    # no constraints nor goal --> make every question in simplified def_constraints relevant
    if (all(e.is_type_constraint_for is not None for e in self.constraints)
    and not goals):
        for def_constraints in out.def_constraints.values():
            for def_constraint in def_constraints:
                q = def_constraint.simplify_with(out.assignments, co_constraints_too=False)
                questions = OrderedSet()
                q.collect(questions, all_=True, co_constraints=False)
                for q in questions:
                    _relevant.append(q)

    # find questions in co_constraints
    to_do = _relevant  # a set of questions and constraints to process
    while to_do:
        to_add = OrderedSet()
        for q in to_do:
            _relevant.append(q)

            # append questions in q to to_add
            q.collect(to_add, all_=True, co_constraints=False)

            # append questions in simplified co_constraints to to_add too
            if type(q) == AppliedSymbol:
                inst = ([q.co_constraint] if q.co_constraint else
                        # out.assignments may not have a co-constraint even when it should
                        [defin.instantiate_definition(q.decl, q.sub_exprs, self)
                            for defin in self.definitions])
                inst = [x.simplify_with(out.assignments, co_constraints_too=False)
                        for x in inst if x]
                to_add.extend(inst)

        to_do = OrderedSet(e for e in to_add if e not in _relevant)

    for q in _relevant:
        ass = self.assignments.get(q.code, None)
        if (ass and not ass.is_certainly_undefined
        and ass.status != S.UNIVERSAL):  #TODO
            ass.relevant = True
    return self
Theory.determine_relevance = determine_relevance


Done = True
