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

Computes the consequences of an expression,
i.e., the sub-expressions that are necessarily true (or false)
if the expression is true (or false)

It has 2 parts:
* symbolic propagation
* Z3 propagation

This module monkey-patches the Expression and Theory classes and sub-classes.
"""
from __future__ import annotations

import time
from copy import copy, deepcopy
from typing import Optional
from z3 import (Solver, sat, unsat, unknown, Not, Or, is_false, is_true,
                is_not, is_eq, Bool, z3types)

from .Assignments import Status as S, Assignments, Assignment
from .Expression import (Expression, AQuantification, ADisjunction,
                         AConjunction, AppliedSymbol, AComparison, AUnary,
                         Brackets, TRUE, FALSE)
from .Parse import str_to_IDP
from .Theory import Theory
from .utils import OrderedSet, IDPZ3Error, NOT_SATISFIABLE
from .Z3_to_IDP import get_interpretations

start = time.process_time()


def _set_consequences_get_changed_choices(self, tag):
    # clear consequences, as these might not be cleared by add_given when
    # running via CLI
    for a in self.assignments.values():
        if a.status == tag:
            self.assignments.assert__(a.sentence, None, S.UNKNOWN)

    removed_choices = {a.sentence.code: a for a in self.previous_assignments.values()
                       if a.status in [S.GIVEN, S.DEFAULT, S.EXPANDED]}
    added_choices = []

    for a in self.assignments.values():
        if a.status in [S.GIVEN, S.DEFAULT, S.EXPANDED]:
            if (a.sentence.code in removed_choices
                    and removed_choices[a.sentence.code].value.same_as(a.value)):
                removed_choices.pop(a.sentence.code)
            else:
                added_choices.append(a)

    if not removed_choices:
        for a in self.previous_assignments.values():
            if (a.status == tag and
                    self.assignments[a.sentence.code].status
                    not in [S.GIVEN, S.EXPANDED, S.DEFAULT]):
                self.assignments.assert__(a.sentence, a.value, a.status)

    # TODO: why is it not ok to use get_core_atoms in this method?

    return removed_choices, added_choices
Theory._set_consequences_get_changed_choices = _set_consequences_get_changed_choices


def _directional_todo(self, removed_choices={}, added_choices=[]):
    """ computes the list of candidate atoms for a new propagation
    * if choices are removed, all previous consequences and removed choices
      should be checked for propagation
    * if choices are added, all unknown atoms should be checked
    """

    todo = {}
    if removed_choices:
        for a in removed_choices.values():
            todo[a.sentence.code] = a.sentence
        for a in self.previous_assignments.values():
            if (a.status in [S.CONSEQUENCE, S.ENV_CONSQ]
                or a.is_certainly_undefined):
                todo[a.sentence.code] = a.sentence

    if added_choices:
        for a in self.get_core_atoms([S.UNKNOWN]):
            todo[a.sentence.code] = a.sentence

    return todo
Theory._directional_todo = _directional_todo


def _batch_propagate(self, tag=S.CONSEQUENCE):
    """ generator of new propagated assignments.  Update self.assignments too.

    uses the method outlined in https://stackoverflow.com/questions/37061360/using-maxsat-queries-in-z3/37061846#37061846
    and in J. Wittocx paper : https://drive.google.com/file/d/19LT64T9oMoFKyuoZ_MWKMKf9tJwGVax-/view?usp=sharing

    This method is not faster than _propagate(), and falls back to it in some cases
    """
    todo = self._directional_todo()
    if todo:
        z3_formula = self.formula()

        solver = Solver(ctx=self.ctx)
        solver.add(z3_formula)
        result = solver.check()
        if result == sat:
            lookup, tests = {}, []
            for q in todo:
                solver.add(q.reified(self) == q.translate(self))  # in case todo contains complex formula
                if solver.check() != sat:
                    # print("Falling back !")
                    yield from self._propagate(tag=tag)
                test = Not(q.reified(self) == solver.model().eval(q.reified(self)))  #TODO compute model once
                tests.append(test)
                lookup[str(test)] = q
            solver.push()
            while True:
                solver.add(Or(tests))
                result = solver.check()
                if result == sat:
                    tests = [t for t in tests if is_false(solver.model().eval(t))]  #TODO compute model once
                    for t in tests:  # reset the other assignments
                        if is_true(solver.model().eval(t)):  #TODO compute model once
                            q = lookup[str(test)]
                            self.assignments.assert__(q, None, S.UNKNOWN)
                elif result == unsat:
                    solver.pop()
                    solver.check()  # not sure why this is needed
                    for test in tests:
                        q = lookup[str(test)]
                        val1 = solver.model().eval(q.reified(self))  #TODO compute model once
                        val = str_to_IDP(q, str(val1))
                        yield self.assignments.assert__(q, val, tag)
                    break
                else:  # unknown
                    # print("Falling back !!")
                    yield from self._propagate(tag=tag)
                    break
            yield "No more consequences."
        elif result == unsat:
            yield NOT_SATISFIABLE
            yield str(z3_formula)
        else:
            yield "Unknown satisfiability."
            yield str(z3_formula)
    else:
        yield "No more consequences."
Theory._batch_propagate = _batch_propagate

def _propagate_inner(self, tag, solver, todo):
    for q in todo.values():
        solver.add(q.reified(self) == q.translate(self))
        # reification in case todo contains complex formula

    res1 = solver.check()

    if res1 == sat:
        model = solver.model()
        interps = get_interpretations(self, model, as_z3=True)
        new_todo = list(todo.values())
        new_todo.extend(self._new_questions_from_model(model, self.assignments))
        valqs = []
        for q in new_todo:
            if (isinstance(q, AppliedSymbol)
            and not q.is_reified()
            and not (q.in_enumeration or q.is_enumerated)):
                assert q.symbol.name in interps, "Internal error"
                maps, _else = interps[q.symbol.name]
                val = maps.get(q.code, _else)  # val may be None
            else:
                val = None
            if val is None:
                val = model.eval(q.reified(self))
            valqs.append((val, q))

        propositions = []
        prop_map = {}
        i = 0
        for (val1, q) in valqs:
            question = q.reified(self)
            if str(val1) == str(question):
                continue  # irrelevant

            is_certainly_undefined = self._is_undefined(solver, q)
            if q.code in self.assignments:
                self.assignments[q.code].is_certainly_undefined = is_certainly_undefined

            if not is_certainly_undefined:
                i += 1
                # Make a new proposition.
                q_symbol = f'__question_{i}'
                bool_q = Bool(q_symbol).translate(solver.ctx)
                solver.add(bool_q == (question == val1))
            propositions.append(bool_q)
            prop_map[q_symbol] = (val1, q)

        # Only query the propositions.
        cons = solver.consequences([], propositions)

        if cons[0] == unknown:
            # It is possible that `consequences` cannot derive anything due to
            # usage of infinite domains and rounding errors. In this case, we fall
            # back on the "old" propagation. For some reason, working with models
            # does not have this limitation (but it is generally much slower).
            yield from self._propagate_through_models(solver, valqs)
            yield "No more consequences."
            return

        assert cons[0] == sat, 'Incorrect solver behavior'

        # Each of the consequences represents a "fixed" value, and should thus be
        # shown as propagated.
        for con in cons[1]:
            q_symbol = str(con.children()[1])
            if q_symbol.startswith('Not('):
                q_symbol = q_symbol[4:-1]
            val1, q = prop_map[q_symbol]
            val = str_to_IDP(q, str(val1))
            yield self.assignments.assert__(q, val, tag)

        yield "No more consequences."
    elif res1 == unsat:
        yield NOT_SATISFIABLE
        yield str(solver.sexpr())
    else:
        assert False, "Incorrect solver behavior"
Theory._propagate_inner = _propagate_inner


def _first_propagate(self, solver: Solver,
                     complete: bool = False):
    """ Determine universals (propagation)

        This is the most complete method of propagation we currently have.
        It works in the following way:
            0. Prepare the solver by adding additional assignments
            1. Generate a single model
            2. For each assertion in the model, add a proposition.
            (Optionally, add a proposition for each function value (see below)
            3. Use Z3's `consequences` to derive which propagations are implied
            4. Translate the propositions back and yield them.

        Optionally, you can set `complete = True` to get a complete
        propagation, in which we also derive negative value assignments for
        functions. By default, propagation won't derive consequences such as
        `Not Belgium = Red`.  By enabling `complete`, this method will truly
        derive every possible consequence, at the cost of speed.

        :arg solver: the solver that should be used.
        :arg complete (bool, optional): whether negative value assignments for
        functions should also be propagated.

        Raises:
            IDPZ3Error: if theory is unsatisfiable
    """
    # NOTE: some universal assignments may be set due to the environment theory
    todo = OrderedSet(a.sentence for a in self.get_core_atoms(
        [S.UNKNOWN, S.EXPANDED, S.DEFAULT, S.GIVEN, S.CONSEQUENCE, S.ENV_CONSQ]))

    solver.push()

    for q in todo:
        solver.add(q.reified(self) == q.translate(self))
        # reification in case todo contains complex formula

    res1 = solver.check()
    if res1 == unsat:
        solver.pop()
        raise IDPZ3Error(NOT_SATISFIABLE)

    assert res1 != unknown, "Incorrect solver behavior"

    # Generate model, and build a set of questions and their values.
    model = solver.model()
    interps = get_interpretations(self, model, as_z3=True)
    new_todo = list(todo.values())
    new_todo.extend(self._new_questions_from_model(model, self.assignments))
    valqs = []
    for q in new_todo:
        if (isinstance(q, AppliedSymbol)
        and not q.is_reified()
        and not (q.in_enumeration or q.is_enumerated)):
            assert q.symbol.name in interps, "Internal error"
            maps, _else = interps[q.symbol.name]
            val = maps.get(q.code, _else)  # val may be None
        else:
            val = None
        if val is None:
            val = model.eval(q.reified(self))
        valqs.append((val, q))

    # Introduce a proposition for each question. We then use Z3's
    # `consequences` to derive which propositions are now implied.
    propositions = []
    prop_map = {}
    for i, (val1, q) in enumerate(valqs):
        question = q.reified(self)
        if str(question) == str(val1):
            # In the case of irrelevant value
            continue

        # Make a new proposition.
        q_symbol = f'__question_{i}'
        bool_q = Bool(q_symbol).translate(solver.ctx)
        solver.add(bool_q == (question == val1))
        propositions.append(bool_q)
        prop_map[q_symbol] = (val1, q)

        if complete and q.type not in ['𝔹', 'ℤ', 'ℝ']:
            # If complete=True, we also want to propagate every possible value
            # of a function. This is the most complete form of propagation, as
            # it will also tell us which function values are now _not_
            # possible, instead of only propagating if the value is fixed.
            values = [x for x in q.decl.range]
            for j, ast_val in enumerate(values):
                q_symbol = f'__question_{i}_{j}_func'
                bool_q = Bool(q_symbol).translate(solver.ctx)
                try:
                    # Ensure that the value is in Z3 form.
                    val2 = ast_val.translate(self)
                except z3types.Z3Exception:
                    pass
                solver.add(bool_q == (question == val2))
                propositions.append(bool_q)
                prop_map[q_symbol] = (ast_val, q)

    # Only query the propositions.
    cons = solver.consequences([], propositions)

    if cons[0] == unknown:
        # It is possible that `consequences` cannot derive anything due to
        # usage of infinite domains and rounding errors. In this case, we fall
        # back on the "old" propagation. For some reason, working with models
        # does not have this limitation (but it is generally much slower).
        yield from self._propagate_through_models(solver, valqs)
        solver.pop()
        return
    assert cons[0] == sat, 'Incorrect solver behavior'

    # Each of the consequences represents a "fixed" value, and should thus be
    # shown as propagated.
    for con in cons[1]:
        q_symbol = str(con.children()[1])
        neg = False
        if q_symbol.startswith('Not('):
            q_symbol = q_symbol[4:-1]
            neg = True

        val, q = prop_map[q_symbol]
        # Convert to AST form if the value is in Z3 form.
        val = str_to_IDP(q, str(val)) if not isinstance(val, Expression) else val

        # In case of `complete=True`, convert the extra function values to
        # comparisons.
        if q_symbol.endswith('_func'):
            q = AComparison(self, '=', [q, val])
            val = FALSE if neg else TRUE

        # FIXME: do we need the test below?
        # ass = self.assignments.get(q.code, None)
        # if (ass and ass.status in [S.GIVEN, S.DEFAULT, S.EXPANDED]
        #    and not ass.value.same_as(val)):
        #     solver.pop()
        #     raise IDPZ3Error(NOT_SATISFIABLE)
        yield self.assignments.assert__(q, val, S.UNIVERSAL)

    solver.pop()
Theory._first_propagate = _first_propagate


def _propagate_through_models(self, solver, valqs):
    # For each question, invert its value and see if it is still satisfiable.
    for val1, q in valqs:
        assert self.extended or not q.is_reified(), \
                "Reified atom should only appear in case of extended theories"
        if str(val1) == str(q.reified(self)):
            continue  # irrelevant
        solver.push()
        solver.add(Not(q.reified(self) == val1))
        res2 = solver.check()
        solver.pop()

        assert res2 != unknown, "Incorrect solver behavior"
        # If it is unsat, the value assignment is a consequence.
        # I.e., there is no possible model in which the value of the question
        # would be different.
        if res2 == unsat:
            val = str_to_IDP(q, str(val1))

            # FIXME: do we need the test below?
            # ass = self.assignments.get(q.code, None)
            # https://gitlab.com/krr/IDP-Z3/-/merge_requests/325#note_1487419405
            # if (ass and ass.status in [S.GIVEN, S.DEFAULT, S.EXPANDED]
            # and not ass.value.same_as(val)):
            #     raise IDPZ3Error(NOT_SATISFIABLE)
            yield self.assignments.assert__(q, val, S.UNIVERSAL)

Theory._propagate_through_models = _propagate_through_models


def _propagate_ignored(self, tag=S.CONSEQUENCE, given_todo=None):
    assert self.ignored_laws, "Internal error"

    solver = self.solver_reified
    solver.push()

    todo = (deepcopy(given_todo) if given_todo else
            {a.sentence.code: a.sentence
            for a in self.assignments.values()
            if a.status not in [S.GIVEN, S.DEFAULT, S.EXPANDED] and
            (a.status != S.STRUCTURE or a.sentence.code in self.ignored_laws)})

    self._add_assignment_ignored(solver)

    yield from self._propagate_inner(tag, solver, todo)
    solver.pop()
Theory._propagate_ignored = _propagate_ignored


def _propagate(self, tag=S.CONSEQUENCE,
               given_todo=None,
               complete: bool = False):
    """generator of new propagated assignments.  Update self.assignments too.

    :arg given_todo: custom collection of assignments to check during propagation.
    given_todo is organized as a dictionary where the keys function to quickly
    check if a certain assignment is in the collection.
    :arg complete (bool, optional): True when requiring a propagation
    including negated function value assignments. Defaults to False.
    """

    global start
    start = time.process_time()

    if self.ignored_laws:
        yield from self._propagate_ignored(tag, given_todo)
        return

    solver = self.solver
    if not self.previous_assignments:
        try:
            yield from self._first_propagate(solver, complete=complete)
            # FIXME: should we return here in the case of CLI?
        except IDPZ3Error:
            yield NOT_SATISFIABLE
            # can't access solver.sexpr()

    removed_choices, added_choices = self._set_consequences_get_changed_choices(tag)

    dir_todo = given_todo is None
    if dir_todo:
        todo = self._directional_todo(removed_choices, added_choices)
    else:
        todo = given_todo.copy()  # shallow copy needed because todo might be adjusted

    if not removed_choices and not added_choices:
        # nothing changed since the previous propagation
        to_remove = []
        for a in todo.values():
            if a.code in self.assignments:
                to_remove.append(a)
                if self.assignments[a.code].status in [S.CONSEQUENCE, S.ENV_CONSQ]:
                    yield self.assignments[a.code]
        for a in to_remove:
            todo.pop(a.code)

    solver.push()

    self._add_assignment(solver)

    yield from self._propagate_inner(tag, solver, todo)
    solver.pop()

    if dir_todo:
        self.previous_assignments = copy(self.assignments)
Theory._propagate = _propagate


def _z3_propagate(self, tag=S.CONSEQUENCE):
    """generator of new propagated assignments.  Update self.assignments too.

    use z3's consequences API (incomplete propagation)
    """
    todo = self._directional_todo()
    if todo:
        z3_todo, unreify = [], {}
        for q in todo:
            z3_todo.append(q.reified(self))
            unreify[q.reified(self)] = q

        z3_formula = self.formula()

        solver = Solver(ctx=self.ctx)
        solver.add(z3_formula)
        result, consqs = solver.consequences([], z3_todo)
        if result == sat:
            for consq in consqs:
                atom = consq.children()[1]
                if is_not(consq):
                    value, atom = FALSE, atom.arg(0)
                else:
                    value = TRUE
                # try to unreify it
                if atom in unreify:
                    yield self.assignments.assert__(unreify[atom], value, tag)
                elif is_eq(consq):
                    assert value == TRUE, f"Internal error in z3_propagate"
                    term = consq.children()[0]
                    if term in unreify:
                        q = unreify[term]
                        val = str_to_IDP(q, consq.children()[1])
                        yield self.assignments.assert__(q, val, tag)
                    else:
                        print("???", str(consq))
                else:
                    print("???", str(consq))
            yield "No more consequences."
            #yield from self._propagate(tag=tag)  # incomplete --> finish with normal propagation
        elif result == unsat:
            yield NOT_SATISFIABLE
            yield str(z3_formula)
        else:
            yield "Unknown satisfiability."
            yield str(z3_formula)
    else:
        yield "No more consequences."
Theory._z3_propagate = _z3_propagate


Done = True
