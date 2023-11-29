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
This module contains methods and functions for the handling of definitions
"""


from __future__ import annotations

from copy import deepcopy
from typing import (Set, Tuple, List, Optional, TYPE_CHECKING)

from .utils import (RESERVED_SYMBOLS, INT, BOOL, Semantics, CO_CONSTR_RECURSION_DEPTH, REAL)
from .Expression import (Expression, catch_error, ZERO, TRUE, FALSE, RecDef, TYPE,
                         Constructor, Symbol, SYMBOL, AppliedSymbol, Operator, AImplication,
                         ARImplication, AAggregate, AUnary, AIfExpr, AComparison,
                         IF, IMPLIES, EQUALS, EQUIV, FORALL, OR, AND)
from .Parse import Definition, Rule, SymbolDeclaration
from .Theory import Theory


# class Definition  ###########################################################

@catch_error
def get_def_constraints(self: Definition,
                        problem: Theory,
                        for_explain: bool = False
                        ) -> dict[Tuple[SymbolDeclaration, Definition], List[Expression]]:
    """returns the constraints for this definition.

    The `instantiables` (of the definition) are expanded in `problem`.

    Args:
        problem (Theory):
            contains the structure for the expansion/interpretation of the constraints

        for_explain (Bool):
            Use implications instead of equivalence, for rule-specific explanations

    Return:
        dict[SymbolDeclaration, Definition, List[Expression]]:
            a mapping from (Symbol, Definition) to the list of constraints
    """
    if self.mode == Semantics.RECDATA:
        out = {}
        for decl in self.renamed:
            # expr = nested if expression, for each rule
            decl.check(decl.out.name in [INT, BOOL],
                       f"Recursive functions of type {decl.out.name} are not supported yet")
            expr = (ZERO if decl.out.name == INT else
                    FALSE if decl.out.name == BOOL else
                    FALSE ) # todo: pick a value in type enumeration
            for rule in self.renamed[decl]:
                val = rule.out if rule.out is not None else TRUE
                expr = IF(rule.body, val, expr)

            vars = sorted(list(self.def_vars[decl.name].values()), key=lambda v: v.name)
            vars = vars[:-1] if decl.out.name != BOOL else vars
            expr = RecDef(self, decl.name, vars, expr.interpret(problem, {}))
            out[decl, self] = [expr]
        return out

    # compute level symbols
    level_symbols: dict[SymbolDeclaration, Symbol] = {}
    for key in self.inductive:
        real = TYPE(REAL)
        real.decl = problem.declarations[REAL]
        symbdec = SymbolDeclaration.make(
            "_"+str(self.id)+"lvl_"+key.name,
            key.arity, key.sorts, real)
        level_symbols[key] = SYMBOL(symbdec.name)
        level_symbols[key].decl = symbdec

    # add level mappings
    instantiables = {}
    for decl, rules in self.canonicals.items():
        rule = rules[0]
        rule.has_finite_domain = all(s.extension(problem.interpretations, problem.extensions)[0] is not None
                                   for s in rule.definiendum.decl.sorts)

        if rule.has_finite_domain or decl in self.inductive:
            # add a constraint containing the definition over the full domain
            if rule.out:
                expr = AppliedSymbol.make(rule.definiendum.symbol,
                                          rule.definiendum.sub_exprs)
                expr.in_head = True
                head = EQUALS([expr, rule.out])
            else:
                head = AppliedSymbol.make(rule.definiendum.symbol,
                                          rule.definiendum.sub_exprs)
                head.in_head = True

            # determine reverse implications, if any
            bodies, implications = [], []
            for r in rules:
                if not decl in self.inductive:
                    bodies.append(r.body)
                    if for_explain and 1 < len(rules):  # not simplified -> no need to make copies
                        implications.append(IMPLIES([r.body, head], r.annotations))
                else:
                    new = r.body.split_equivalences()
                    bodies.append(new)
                    if for_explain:
                        new = deepcopy(new).add_level_mapping(level_symbols,
                                             rule.definiendum, False, False, self.mode)
                        implications.append(IMPLIES([new, head], r.annotations))

            all_bodies = OR(bodies)
            if not decl in self.inductive:  # i.e., function with finite domain
                if implications:  # already contains reverse implications
                    implications.append(IMPLIES([head, all_bodies], self.annotations))
                else:
                    implications = [EQUIV([head, all_bodies], self.annotations)]
            else:  # i.e., predicate
                if not implications:  # no reverse implication
                    new = deepcopy(all_bodies).add_level_mapping(level_symbols,
                                             rule.definiendum, False, False, self.mode)
                    implications = [IMPLIES([new, deepcopy(head)], self.annotations)]
                all_bodies = deepcopy(all_bodies).add_level_mapping(level_symbols,
                                        rule.definiendum, True, True, self.mode)
                implications.append(IMPLIES([head, all_bodies], self.annotations))
            instantiables[decl] = implications

    out = {}
    for decl, bodies in instantiables.items():
        quantees = self.canonicals[decl][0].quantees  # take quantee from 1st renamed rule
        expr = [FORALL(quantees, e, e.annotations).interpret(problem, {})
                for e in bodies]
        out[decl, self] = expr
    return out
Definition.get_def_constraints = get_def_constraints

@catch_error
def instantiate_definition(self: Definition, decl, new_args, theory) -> Optional[Expression]:
    rule = self.clarks.get(decl, None)
    # exclude inductive and recursive definitions
    if rule and self.mode != Semantics.RECDATA and decl not in self.inductive:
        instantiable = all(  # finite domain or not a variable
            s.extension(theory.interpretations, theory.extensions)[0] is not None
            or not v.has_variables()
            for s, v in zip(rule.definiendum.decl.sorts, new_args))

        if not instantiable:
            return None

        key = str(new_args)
        if (decl, key) in self.cache:
            return self.cache[decl, key]

        if self.inst_def_level + 1 > CO_CONSTR_RECURSION_DEPTH:
            return None
        self.inst_def_level += 1
        self.cache[decl, key] = None

        out = rule.instantiate_definition(new_args, theory)

        self.cache[decl, key] = out
        self.inst_def_level -= 1
        return out
    return None
Definition.instantiate_definition = instantiate_definition


# class Rule  ###########################################################

@catch_error
def instantiate_definition(self: Rule,
                           new_args: List[Expression],
                           theory: Theory
                           ) -> Expression:
    """Create an instance of the definition for new_args, and interpret it for theory.

    Args:
        new_args ([Expression]): tuple of arguments to be applied to the defined symbol
        theory (Theory): the context for the interpretation

    Returns:
        Expression: a boolean expression
    """
    out = self.body  # in case there are no arguments
    instance = AppliedSymbol.make(self.definiendum.symbol, new_args)
    instance.in_head = True
    self.check(len(self.definiendum.sub_exprs) == len(new_args),
                "Internal error")
    subs = dict(zip([e.name for e in self.definiendum.sub_exprs], new_args))

    if self.definiendum.decl.type == BOOL:  # a predicate
        out = EQUIV([instance, out])
    else:
        subs[self.out.name] = instance
    out = out.interpret(theory, subs)
    out.block = self.block
    return out
Rule.instantiate_definition = instantiate_definition


## collect_nested_symbols ####################################################

# Expression
def collect_nested_symbols(self,
                            symbols: Set[SymbolDeclaration],
                            is_nested: bool
                            ) -> Set[SymbolDeclaration]:
    """ returns the set of symbol declarations that occur (in)directly
    under an aggregate or some nested term, where is_nested is flipped
    to True the moment we reach such an expression

    returns {SymbolDeclaration}
    """
    for e in self.sub_exprs:
        e.collect_nested_symbols(symbols, is_nested)
    return symbols
Expression.collect_nested_symbols = collect_nested_symbols


# AIfExpr
def collect_nested_symbols(self, symbols, is_nested):
    return Expression.collect_nested_symbols(self, symbols, True)
AIfExpr.collect_nested_symbols = collect_nested_symbols


# Operator
def collect_nested_symbols(self, symbols, is_nested):
    return Expression.collect_nested_symbols(self, symbols,
            is_nested if self.operator[0] in ['∧','∨','⇒','⇐','⇔'] else True)
Operator.collect_nested_symbols = collect_nested_symbols


# AAggregate
def collect_nested_symbols(self, symbols, is_nested):
    return Expression.collect_nested_symbols(self, symbols, True)
AAggregate.collect_nested_symbols = collect_nested_symbols


# AppliedSymbol
def collect_nested_symbols(self, symbols, is_nested):
    if is_nested and (hasattr(self, 'decl') and self.decl
        and type(self.decl) != Constructor
        and not self.decl.name in RESERVED_SYMBOLS):
        symbols.add(self.decl)
    for e in self.sub_exprs:
        e.collect_nested_symbols(symbols, True)
    return symbols
AppliedSymbol.collect_nested_symbols = collect_nested_symbols



## add_level_mapping ####################################################

# Expression
def add_level_mapping(self,
                        level_symbols: dict[SymbolDeclaration, Symbol],
                        head: AppliedSymbol,
                        pos_justification: bool,
                        polarity: bool,
                        mode: Semantics
                        ) -> Expression:
    """Returns an expression where level mapping atoms (e.g., lvl_p > lvl_q)
        are added to atoms containing recursive symbols.

    Arguments:
        - level_symbols (dict[SymbolDeclaration, Symbol]): the level mapping
            symbols as well as their corresponding recursive symbols
        - head (AppliedSymbol): head of the rule we are adding level mapping
            symbols to.
        - pos_justification (Bool): whether we are adding symbols to the
            direct positive justification (e.g., head => body) or direct
            negative justification (e.g., body => head) part of the rule.
        - polarity (Bool): whether the current expression occurs under
            negation.
    """
    return (self.update_exprs((e.add_level_mapping(level_symbols, head, pos_justification, polarity, mode)
                                for e in self.sub_exprs))
                .annotate1())  # update .variables
Expression.add_level_mapping = add_level_mapping


# AImplication
def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
    sub_exprs = [self.sub_exprs[0].add_level_mapping(level_symbols, head, pos_justification, not polarity, mode),
                    self.sub_exprs[1].add_level_mapping(level_symbols, head, pos_justification, polarity, mode)]
    return self.update_exprs(sub_exprs).annotate1()
AImplication.add_level_mapping = add_level_mapping


# ARImplication
def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
    sub_exprs = [self.sub_exprs[0].add_level_mapping(level_symbols, head, pos_justification, polarity, mode),
                    self.sub_exprs[1].add_level_mapping(level_symbols, head, pos_justification, not polarity, mode)]
    return self.update_exprs(sub_exprs).annotate1()
ARImplication.add_level_mapping = add_level_mapping

# AUnary
def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
    sub_exprs = (e.add_level_mapping(level_symbols, head,
                                        pos_justification,
                                        not polarity
                                        if self.operator == '¬' else polarity,
                                        mode)
                    for e in self.sub_exprs)
    return self.update_exprs(sub_exprs).annotate1()
AUnary.add_level_mapping = add_level_mapping


# AppliedSymbol
def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
    assert head.symbol.decl in level_symbols, \
            f"Internal error in level mapping: {self}"
    if (self.symbol.decl not in level_symbols
        or self.in_head
        or mode in [Semantics.RECDATA, Semantics.COMPLETION]
        or (mode == Semantics.STABLE and pos_justification != polarity)):
        return self
    else:
        if mode in [Semantics.WELLFOUNDED, Semantics.STABLE]:
            op = ('>' if pos_justification else '≥') \
                if polarity else ('≤' if pos_justification else '<')
        elif mode == Semantics.KRIPKEKLEENE:
            op = '>' if polarity else '≤'
        else:
            assert mode == Semantics.COINDUCTION, \
                    f"Internal error: {mode}"
            op = ('≥' if pos_justification else '>') \
                if polarity else ('<' if pos_justification else '≤')
        comp = AComparison.make(op, [
            AppliedSymbol.make(level_symbols[head.symbol.decl], head.sub_exprs),
            AppliedSymbol.make(level_symbols[self.symbol.decl], self.sub_exprs)
        ])
        if polarity:
            return AND([comp, self])
        else:
            return OR([comp, self])
AppliedSymbol.add_level_mapping = add_level_mapping


Done = True