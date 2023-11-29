# cython: binding=True

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

Methods to ground / interpret a theory in a data structure

* expand quantifiers
* replace symbols interpreted in the structure by their interpretation
* instantiate definitions

This module monkey-patches the ASTNode class and sub-classes.

( see docs/zettlr/Substitute.md )

"""
from __future__ import annotations

from copy import copy, deepcopy
from itertools import product
from typing import List, Callable, Optional, Tuple

from .Assignments import Status as S
from .Parse import (Import, TypeDeclaration, SymbolDeclaration,
                    SymbolInterpretation, FunctionEnum, Enumeration, TupleIDP,
                    ConstructedFrom, Definition, Rule)
from .Expression import (catch_error, RecDef, Symbol, SYMBOL, AIfExpr, IF,
                         SymbolExpr, Expression, Constructor, AQuantification,
                         Type, FORALL, IMPLIES, AND, AAggregate, EQUIV, EQUALS,
                         OR, AppliedSymbol, UnappliedSymbol, Quantee, Variable,
                         VARIABLE, TRUE, FALSE, Number, ZERO, Extension)
from .Theory import Theory
from .utils import (BOOL, INT, RESERVED_SYMBOLS, CONCEPT, OrderedSet, DEFAULT,
                    GOAL_SYMBOL, EXPAND, CO_CONSTR_RECURSION_DEPTH, Semantics)


# class Import  ###########################################################

@catch_error
def interpret(self: Import, problem: Theory):
    pass
Import.interpret = interpret


# class TypeDeclaration  ###########################################################

@catch_error
def interpret(self: TypeDeclaration, problem: Theory):
    interpretation = problem.interpretations.get(self.name, None)
    if self.name in [BOOL, CONCEPT]:
        self.translate(problem)
        ranges = [c.interpret(problem).range for c in self.constructors]
        ext = ([[t] for r in ranges for t in r], None)
        problem.extensions[self.name] = ext
    else:
        self.check(interpretation is not None
                   and hasattr(interpretation, 'enumeration'),
                   f'Expected an interpretation for type {self.name}')

        enum = interpretation.enumeration.interpret(problem)
        self.interpretation = interpretation
        self.constructors = enum.constructors
        self.translate(problem)

        if self.constructors is not None:
            for c in self.constructors:
                c.interpret(problem)

        # update problem.extensions
        ext = enum.extensionE(problem.interpretations, problem.extensions)
        problem.extensions[self.name] = ext

        # needed ?
        # if (isinstance(self.interpretation.enumeration, Ranges)
        # and self.interpretation.enumeration.tuples):
        #     # add condition that the interpretation is total over the infinite domain
        #     # ! x in N: type(x) <=> enum.contains(x)
        #     t = TYPE(self.type)  # INT, REAL or DATE
        #     t.decl, t.type = self, self.type
        #     var = VARIABLE(f"${self.name}!0$",t)
        #     q_vars = { f"${self.name}!0$": var}
        #     quantees = [Quantee.make(var, subtype=t)]
        #     expr1 = AppliedSymbol.make(SYMBOL(self.name), [var])
        #     expr1.decl = self
        #     expr2 = enum.contains(list(q_vars.values()), True)
        #     expr = EQUALS([expr1, expr2])
        #     constraint = FORALL(quantees, expr)
        #     constraint.annotations['reading'] = f"Enumeration of {self.name} should cover its domain"
        #     problem.constraints.append(constraint)
TypeDeclaration.interpret = interpret


# class SymbolDeclaration  ###########################################################

@catch_error
def interpret(self: SymbolDeclaration, problem: Theory):
    assert all(isinstance(s, Type) for s in self.sorts), 'internal error'

    symbol = SYMBOL(self.name)
    symbol.decl = self
    symbol.type = symbol.decl.type

    # determine the extension, i.e., (superset, filter)
    extensions = [s.extension(problem.interpretations, problem.extensions)
                for s in self.sorts]
    if any(e[0] is None for e in extensions):
        superset = None
    else:
        superset = list(product(*([ee[0] for ee in e[0]] for e in extensions)))

    filters = [e[1] for e in extensions]
    def filter(args):
        out = AND([f([deepcopy(t)]) if f is not None else TRUE
                    for f, t in zip(filters, args)])
        if self.out.decl.name == BOOL:
            out = AND([out, deepcopy(AppliedSymbol.make(symbol, args))])
        return out

    if self.out.decl.name == BOOL:
        problem.extensions[self.name] = (superset, filter)

    (range, _) = self.out.extension(problem.interpretations, problem.extensions)
    if range is None:
        self.range = []
    else:
        self.range = [e[0] for e in range]

    # create instances + empty assignment
    if self.name not in RESERVED_SYMBOLS and superset is not None:
        self.instances = {}
        for args in superset:
            expr = AppliedSymbol.make(symbol, args)
            self.instances[expr.code] = expr
            problem.assignments.assert__(expr, None, S.UNKNOWN)

    # interpret the enumeration
    if self.name in problem.interpretations and self.name != GOAL_SYMBOL:
        problem.interpretations[self.name].interpret(problem)

    # create type constraints
    if type(self.instances) == dict and self.out.decl.name != BOOL:
        for expr in self.instances.values():
            # add type constraints to problem.constraints
            # ! (x,y) in domain: range(f(x,y))
            range_condition = self.out.has_element(deepcopy(expr),
                                problem.interpretations, problem.extensions)
            if range_condition.same_as(TRUE):
                break
            range_condition = range_condition.interpret(problem, {})
            constraint = IMPLIES([filter(expr.sub_exprs), range_condition])
            constraint.is_type_constraint_for = self.name
            constraint.annotations['reading'] = f"Possible values for {expr}"
            problem.constraints.append(constraint)
SymbolDeclaration.interpret = interpret


# class Definition  ###########################################################

@catch_error
def interpret(self: Definition, problem: Theory):
    """updates problem.def_constraints, by expanding the definitions

    Args:
        problem (Theory):
            containts the enumerations for the expansion; is updated with the expanded definitions
    """
    self.cache = {}  # reset the cache
    problem.def_constraints.update(self.get_def_constraints(problem))
Definition.interpret = interpret


# class SymbolInterpretation  ###########################################################

@catch_error
def interpret(self: SymbolInterpretation, problem: Theory):
    status = S.DEFAULT if self.block.name == DEFAULT else S.STRUCTURE
    assert not self.is_type_enumeration, "Internal error"
    if not self.name in [GOAL_SYMBOL, EXPAND]:
        decl = problem.declarations[self.name]
        assert isinstance(decl, SymbolDeclaration), "Internal error"
        # update problem.extensions
        if self.symbol.decl.out.decl.name == BOOL:  # predicate
            extension = [t.args for t in self.enumeration.tuples]
            problem.extensions[self.symbol.name] = (extension, None)

        enumeration = self.enumeration  # shorthand
        self.check(all(len(t.args) == self.symbol.decl.arity
                            + (1 if type(enumeration) == FunctionEnum else 0)
                        for t in enumeration.tuples),
            f"Incorrect arity of tuples in Enumeration of {self.symbol}.  Please check use of ',' and ';'.")

        lookup = {}
        if hasattr(decl, 'instances') and decl.instances and self.default:
            lookup = { ",".join(str(a) for a in applied.sub_exprs): self.default
                    for applied in decl.instances.values()}
        if type(enumeration) == FunctionEnum:
            lookup.update( (','.join(str(a) for a in t.args[:-1]), t.args[-1])
                        for t in enumeration.sorted_tuples)
        else:
            lookup.update( (t.code, TRUE)
                            for t in enumeration.sorted_tuples)
        enumeration.lookup = lookup

        # update problem.assignments with data from enumeration
        for t in enumeration.tuples:

            # check that the values are in the range
            if type(self.enumeration) == FunctionEnum:
                args, value = t.args[:-1], t.args[-1]
                condition = decl.has_in_range(value,
                            problem.interpretations, problem.extensions)
                self.check(not condition.same_as(FALSE),
                           f"{value} is not in the range of {self.symbol.name}")
                if not condition.same_as(TRUE):
                    problem.constraints.append(condition)
            else:
                args, value = t.args, TRUE

            # check that the arguments are in the domain
            a = (str(args) if 1<len(args) else
                    str(args[0]) if len(args)==1 else
                    "()")
            self.check(len(args) == decl.arity,
                       f"Incorrect arity of {a} for {self.name}")
            condition = decl.has_in_domain(args,
                            problem.interpretations, problem.extensions)
            self.check(not condition.same_as(FALSE),
                       f"{a} is not in the domain of {self.symbol.name}")
            if not condition.same_as(TRUE):
                problem.constraints.append(condition)

            # check duplicates
            expr = AppliedSymbol.make(self.symbol, args)
            self.check(expr.code not in problem.assignments
                or problem.assignments[expr.code].status == S.UNKNOWN,
                f"Duplicate entry in structure for '{self.name}': {str(expr)}")

            # add to problem.assignments
            e = problem.assignments.assert__(expr, value, status)
            if (status == S.DEFAULT  # for proper display in IC
                and type(self.enumeration) == FunctionEnum):
                problem.assignments.assert__(e.formula(), TRUE, status)

        if self.default is not None:
            if decl.instances is not None:
                # fill the default value in problem.assignments
                for code, expr in decl.instances.items():
                    if (code not in problem.assignments
                        or problem.assignments[code].status != status):
                        e = problem.assignments.assert__(expr, self.default, status)
                        if (status == S.DEFAULT  # for proper display in IC
                            and type(self.enumeration) == FunctionEnum
                            and self.default.type != BOOL):
                            problem.assignments.assert__(e.formula(), TRUE, status)

        elif self.sign == '≜':
            # add condition that the interpretation is total
            # over the domain specified by the type signature
            # ! x in domain(f): enum.contains(x)
            q_vars = { f"${sort.decl.name}!{str(i)}$":
                       VARIABLE(f"${sort.decl.name}!{str(i)}$", sort)
                       for i, sort in enumerate(decl.sorts)}
            quantees = [Quantee.make(v, sort=v.sort) for v in q_vars.values()]

            # is the domain of `self` enumerable ?
            constraint1 = FORALL(quantees, FALSE)
            get_supersets(constraint1, problem)
            if constraint1.sub_exprs[0] == FALSE:  # no filter added
                # the domain is enumerable => do the check immediately
                domain = set(str(flatten(d)) for d in product(*constraint1.supersets))
                if type(self.enumeration) == FunctionEnum:
                    enumeration = set(str(d.args[:-1]) for d in self.enumeration.tuples)
                else:
                    enumeration = set(str(d.args) for d in self.enumeration.tuples)
                self.check(domain == enumeration, f"Enumeration of {self.name} should cover its domain")
            else:  # add a constraint to the problem, to be solved by Z3
                # test case: tests/1240 FO{Core, Sugar, Int, PF)/LivingBeing.idp
                expr = self.enumeration.contains(list(q_vars.values()), True)
                constraint = FORALL(quantees, expr).interpret(problem, {})
                constraint.annotations['reading'] = f"Enumeration of {self.name} should cover its domain"
                problem.constraints.append(constraint)
SymbolInterpretation.interpret = interpret


# class Enumeration  ###########################################################

@catch_error
def interpret(self: Enumeration, problem: Theory) -> Enumeration:
    return self
Enumeration.interpret = interpret


# class ConstructedFrom  ###########################################################

@catch_error
def interpret(self: ConstructedFrom, problem: Theory) -> ConstructedFrom:
    self.tuples = OrderedSet()
    for c in self.constructors:
        c.interpret(problem)
        if c.range is None:
            self.tuples = None
            return self
        self.tuples.extend(TupleIDP(args=[e]) for e in c.range)
    return self
ConstructedFrom.interpret = interpret


# class Constructor  ###########################################################

@catch_error
def interpret(self: Constructor, problem: Theory) -> Constructor:
    # assert all(s.decl and isinstance(s.decl.out, Type) for s in self.sorts), 'Internal error'
    if not self.sorts:
        self.range = [UnappliedSymbol.construct(self)]
    elif any(s.type == self.type for s in self.sorts):  # recursive data type
        self.range = None
    else:
        # assert all(isinstance(s.decl, SymbolDeclaration) for s in self.sorts), "Internal error"
        extensions = [s.decl.out.extension(problem.interpretations, problem.extensions)
                      for s in self.sorts]
        if any(e[0] is None for e in extensions):
            self.range = None
        else:
            self.check(all(e[1] is None for e in extensions),  # no filter in the extension
                       f"Type signature of constructor {self.name} must have a given interpretation")
            self.range = [AppliedSymbol.construct(self, es)
                          for es in product(*[[ee[0] for ee in e[0]] for e in extensions])]
    return self
Constructor.interpret = interpret


# class Expression  ###########################################################

def interpret(self: Expression,
              problem: Optional[Theory],
              subs: dict[str, Expression]
              ) -> Expression:
    """expand quantifiers and replace symbols interpreted in the structure
    by their interpretation

    Args:
        self: the expression to be interpreted
        problem: the theory to be applied
        subs: a dictionary mapping variable names to their value

    Returns:
        Expression: the interpreted expression
    """
    if self.is_type_constraint_for:
        return self
    _prepare_interpret(self, problem, subs)
    return self._interpret(problem, subs)
Expression.interpret = interpret

def _prepare_interpret(self: Expression,
              problem: Optional[Theory],
              subs: dict[str, Expression]
              ):
    """Prepare the interpretation by transforming quantifications and aggregates

    """

    for e in self.sub_exprs:
        _prepare_interpret(e, problem, subs)

    if isinstance(self, AQuantification) or isinstance(self, AAggregate):
        # type inference
        if 0 < len(self.sub_exprs):  # in case it was simplified away
            inferred = self.sub_exprs[0].type_inference()
            for q in self.quantees:
                if not q.sub_exprs:
                    assert len(q.vars) == 1 and q.arity == 1, \
                        f"Internal error: interpret {q}"
                    var = q.vars[0][0]
                    self.check(var.name in inferred,
                                f"can't infer type of {var.name}")
                    var.sort = inferred[var.name]
                    q.sub_exprs = [inferred[var.name]]
        get_supersets(self, problem)



def clone_when_necessary(func):
    @catch_error
    def inner_function(self, problem, subs):
        if self.is_value():
            return self
        if subs:
            self = copy(self)  # shallow copy !
            self.annotations = copy(self.annotations)
        out = func(self, problem, subs)
        return out
    return inner_function

@clone_when_necessary
def _interpret(self: Expression,
               problem: Optional[Theory],
               subs: dict[str, Expression]
               ) -> Expression:
    """ uses information in the problem and its vocabulary to:
    - expand quantifiers in the expression
    - simplify the expression using known assignments and enumerations
    - instantiate definitions

    This method creates a copy when necessary.

    Args:
        problem (Theory): the Theory to apply

        subs: a dictionary holding the value of the free variables of self

    Returns:
        Expression: the resulting expression
    """
    out = self.update_exprs(e._interpret(problem, subs) for e in self.sub_exprs)
    _finalize(out, subs)
    return out
Expression._interpret = _interpret

@catch_error
def _finalize(self: Expression, subs: dict[str, Expression]):
    """update self.variables and reading"""
    if subs:
        self.code = str(self)
        self.annotations['reading'] = self.code
    return self


# class Type ###########################################################

@catch_error
def extension(self, interpretations: dict[str, SymbolInterpretation],
              extensions: dict[str, Extension]
              ) -> Extension:
    """returns the extension of a Type, given some interpretations.

    Normally, the extension is already in `extensions`.
    However, for Concept[T->T], an additional filtering is applied.

    Args:
        interpretations (dict[str, SymbolInterpretation]):
        the known interpretations of types and symbols

    Returns:
        Extension: a superset of the extension of self,
        and a function that, given arguments, returns an Expression that says
        whether the arguments are in the extension of self
    """
    if self.code not in extensions:
        self.check(self.name == CONCEPT, "internal error")
        assert (self.out
                and extensions is not None
                and extensions[CONCEPT] is not None), "internal error"  # Concept[T->T]
        ext = extensions[CONCEPT][0]
        assert isinstance(ext, List) , "Internal error"
        out = [v for v in ext
                if type(v[0]) == UnappliedSymbol
                and v[0].decl.symbol.decl.arity == len(self.ins)
                and isinstance(v[0].decl.symbol.decl, SymbolDeclaration)
                and v[0].decl.symbol.decl.out == self.out
                and len(v[0].decl.symbol.decl.sorts) == len(self.ins)
                and all(s == q
                        for s, q in zip(v[0].decl.symbol.decl.sorts,
                                        self.ins))]
        extensions[self.code] = (out, None)
    return extensions[self.code]
Type.extension = extension

# Class AQuantification  ######################################################

def get_supersets(self: AQuantification | AAggregate, problem: Optional[Theory]):
    """determine the extent of the variables, if possible,
    and add a filter to the quantified expression if needed.
    This is used to ground quantification over unary predicates.

    Example:
        type T := {1,2,3}
        p : T -> Bool  // p is a subset of T
        !x in p: q(x)

        The formula is equivalent to `!x in T: p(x) => q(x).`
        -> The superset of `p` is `{1,2,3}`, the filter is `p(x)`.
        The grounding is `(p(1)=>q(1)) & (p(2)=>q(2)) & (p(3)=>q(3))`

        If p is enumerated (`p:={1,2}`) in a structure, however,
        the superset is now {1,2} and there is no need for a filter.
        The grounding is `q(1) & q(2)`

    Result:
        `self.supersets` is updated to contain the supersets
        `self.sub_exprs` are updated with the appropriate filters
    """
    self.new_quantees, self.vars1, self.supersets = [], [], []
    for q in self.quantees:
        domain = q.sub_exprs[0]

        if problem:
            if isinstance(domain, Type):  # quantification over type / Concepts
                (superset, filter) = domain.extension(problem.interpretations,
                                                    problem.extensions)
            elif type(domain) == SymbolExpr:
                return
            elif type(domain) == Symbol and domain.decl:
                self.check(domain.decl.out.type == BOOL,
                            f"{domain} is not a type or predicate")
                assert domain.decl.name in problem.extensions, "internal error"
                (superset, filter) = problem.extensions[domain.decl.name]
            else:
                self.check(False, f"Can't resolve the domain of {str(q.vars)}")
        else:
            (superset, filter) = None, None

        assert hasattr(domain, "decl"), "Internal error"
        arity = domain.decl.arity
        for vars in q.vars:
            self.check(len(vars) == arity, f"Incorrect arity for {domain}")
            if problem and filter:
                self.sub_exprs = [_add_filter(self.q, f, filter, vars, problem)
                                  for f in self.sub_exprs]

        self.vars1.extend(flatten(q.vars))

        if superset is None:
            self.new_quantees.append(q)
            self.supersets.extend([q] for q in q.vars)  # replace the variable by itself
        else:
            self.supersets.extend([superset]*len(q.vars))


def _add_filter(q: str, expr: Expression, filter: Callable, args: List[Variable],
                theory: Theory) -> Expression:
    """add `filter(args)` to `expr` quantified by `q`

    Example: `_add_filter('∀', TRUE, filter, [1], theory)` returns `filter([1]) => TRUE`

    Args:
        q: the type of quantification
        expr: the quantified expression
        filter: a function that returns an Expression for some arguments
        args:the arguments to be applied to filter

    Returns:
        Expression: `expr` extended with appropriate filter
    """
    applied = filter(args)
    if q == '∀':
        out = IMPLIES([applied, expr])
    elif q == '∃':
        out = AND([applied, expr])
    else:  # aggregate
        if isinstance(expr, AIfExpr):  # cardinality
            # if a then b else 0 -> if (applied & a) then b else 0
            arg1 = AND([applied, expr.sub_exprs[0]])
            out = IF(arg1, expr.sub_exprs[1], expr.sub_exprs[2])
        else:  # sum
            out = IF(applied, expr, Number(number="0"))
    return out

def flatten(a):
    # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
    out = []
    for sublist in a:
        out.extend(sublist)
    return out

@clone_when_necessary
def _interpret(self: AQuantification | AAggregate,
               problem: Optional[Theory],
               subs: dict[str, Expression]
               ) -> Expression:
    """apply information in the problem and its vocabulary

    Args:
        problem (Theory): the problem to be applied

    Returns:
        Expression: the expanded quantifier expression
    """
    # This method is called by AAggregate._interpret !

    if not self.quantees and not subs:  # already expanded
        return Expression._interpret(self, problem, subs)

    if not self.supersets:
        # interpret quantees
        for q in self.quantees: # for !x in $(output_domain(s,1))
            q.sub_exprs = [e._interpret(problem, subs) for e in q.sub_exprs]
        get_supersets(self, problem)

    assert self.new_quantees is not None and self.vars1 is not None, "Internal error"
    self.quantees = self.new_quantees
    # expand the formula by the cross-product of the supersets, and substitute per `subs`
    forms, subs1 = [], copy(subs)
    for f in self.sub_exprs:
        for vals in product(*self.supersets):
            vals1 = flatten(vals)
            subs1.update((var.code, val) for var, val in zip(self.vars1, vals1))
            new_f2 = f._interpret(problem, subs1)
            forms.append(new_f2)

    out = self.update_exprs(f for f in forms)
    return out
AQuantification._interpret = _interpret


# Class AAggregate  ######################################################

@clone_when_necessary
def _interpret(self: AAggregate,
               problem: Optional[Theory],
               subs: dict[str, Expression]
               ) -> Expression:
    assert self.annotated, f"Internal error in interpret"
    return AQuantification._interpret(self, problem, subs)
AAggregate._interpret = _interpret


# Class AppliedSymbol  ##############################################

@clone_when_necessary
def _interpret(self: AppliedSymbol,
               problem: Optional[Theory],
               subs: dict[str, Expression]
               ) -> Expression:
    # interpret the symbol expression, if any
    if type(self.symbol) == SymbolExpr and self.symbol.is_intentional():  # $(x)()
        self.symbol = self.symbol._interpret(problem, subs)
        if type(self.symbol) == Symbol:  # found $(x)
            self.check(len(self.sub_exprs) == len(self.symbol.decl.sorts),
                        f"Incorrect arity for {self.code}")
            kwargs = ({'is_enumerated': self.is_enumerated} if self.is_enumerated else
                        {'in_enumeration': self.in_enumeration} if self.in_enumeration else
                        {})
            out = AppliedSymbol.make(self.symbol, self.sub_exprs, **kwargs)
            out.original = self
            self = out

    # interpret the arguments
    sub_exprs = [e._interpret(problem, subs) for e in self.sub_exprs]
    out = self.update_exprs(e for e in sub_exprs)
    _finalize(out, subs)
    if out.is_value():
        return out

    # interpret the AppliedSymbol
    value, co_constraint = None, None
    if out.decl and problem:
        if out.is_enumerated:
            assert out.decl.type != BOOL, \
                f"Can't use 'is enumerated' with predicate {out.decl.name}."
            if out.decl.name in problem.interpretations:
                interpretation = problem.interpretations[out.decl.name]
                if interpretation.default is not None:
                    out.as_disjunction = TRUE
                else:
                    out.as_disjunction = interpretation.enumeration.contains(sub_exprs, True,
                        interpretations=problem.interpretations, extensions=problem.extensions)
                if out.as_disjunction.same_as(TRUE) or out.as_disjunction.same_as(FALSE):
                    value = out.as_disjunction
                out.as_disjunction.annotations = out.annotations
        elif out.in_enumeration:
            # re-create original Applied Symbol
            core = deepcopy(AppliedSymbol.make(out.symbol, sub_exprs))
            out.as_disjunction = out.in_enumeration.contains([core], False,
                        interpretations=problem.interpretations, extensions=problem.extensions)
            if out.as_disjunction.same_as(TRUE) or out.as_disjunction.same_as(FALSE):
                value = out.as_disjunction
            out.as_disjunction.annotations = out.annotations
        elif out.decl.name in problem.interpretations:
            interpretation = problem.interpretations[out.decl.name]
            if interpretation.block.name != DEFAULT:
                f = interpretation.interpret_application
                value = f(0, out, sub_exprs)
        if not out.in_head:
            # instantiate definition (for relevance)
            inst = [defin.instantiate_definition(out.decl, sub_exprs, problem)
                    for defin in problem.definitions]
            inst = [x for x in inst if x]
            if inst:
                co_constraint = AND(inst)
            elif self.co_constraint:
                co_constraint = self.co_constraint.interpret(problem, subs)

        out = (value if value else
               out._change(sub_exprs=sub_exprs, co_constraint=co_constraint))
    return out
AppliedSymbol._interpret = _interpret


# Class Variable  #######################################################

@catch_error
def _interpret(self: Variable,
              problem: Optional[Theory],
              subs: dict[str, Expression]
              ) -> Expression:
    if self.sort:
        self.sort = self.sort._interpret(problem, subs)
    out = subs.get(self.code, self)
    return out
Variable._interpret = _interpret


Done = True
