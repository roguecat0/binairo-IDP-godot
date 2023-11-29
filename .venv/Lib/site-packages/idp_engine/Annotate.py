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

Methods to annotate the Abstract Syntax Tree (AST) of an IDP-Z3 program.

"""
from __future__ import annotations

from copy import copy, deepcopy
from itertools import chain
import string

from .Parse import (Vocabulary, Import, TypeDeclaration, Declaration,
                    SymbolDeclaration, VarDeclaration, TheoryBlock, Definition,
                    Rule, Structure, SymbolInterpretation, Enumeration,
                    FunctionEnum, TupleIDP, ConstructedFrom, Display)
from .Expression import (Expression, Symbol, SYMBOL, Type, TYPE,
                         Constructor, CONSTRUCTOR, AIfExpr, IF,
                         AQuantification, Quantee, ARImplication, AImplication,
                         AEquivalence, Operator, AComparison, AUnary,
                         AAggregate, AppliedSymbol, UnappliedSymbol, Variable,
                         VARIABLE, Brackets, SymbolExpr, Number, NOT,
                         EQUALS, AND, OR, FALSE, ZERO, IMPLIES, FORALL, EXISTS)

from .utils import (BOOL, INT, REAL, DATE, CONCEPT, RESERVED_SYMBOLS,
                    OrderedSet, Semantics)


# Class Vocabulary  #######################################################

def annotate(self, idp):
    self.idp = idp

    # process Import and determine the constructors of CONCEPT
    temp = {}  # contains the new self.declarations
    for s in self.declarations:
        if isinstance(s, Import):
            other = self.idp.vocabularies[s.name]
            for s1 in other.declarations:
                if s1.name in temp:
                    s.check(str(temp[s1.name]) == str(s1),
                            f"Inconsistent declaration for {s1.name}")
                temp[s1.name] = s1
        else:
            s.block = self
            s.check(s.name not in temp or s.name in RESERVED_SYMBOLS,
                    f"Duplicate declaration of {s.name}")
            temp[s.name] = s
    temp[CONCEPT].constructors=([CONSTRUCTOR(f"`{s}")
                                 for s in [BOOL, INT, REAL, DATE, CONCEPT]]
                               +[CONSTRUCTOR(f"`{s.name}")
                                 for s in temp.values()
                                 if s.name not in RESERVED_SYMBOLS
                                 and type(s) in Declaration.__args__])
    self.declarations = list(temp.values())

    # annotate declarations
    for s in self.declarations:
        s.annotate(self)  # updates self.symbol_decls

    concepts = self.symbol_decls[CONCEPT]
    for constructor in concepts.constructors:
        constructor.symbol = (SYMBOL(constructor.name[1:])
                                .annotate(self, {}))

    # populate .map of CONCEPT
    for c in concepts.constructors:
        assert not c.sorts, "Internal error"
        concepts.map[str(c)] = UnappliedSymbol.construct(c)
Vocabulary.annotate = annotate


# Class TypeDeclaration  #######################################################

def annotate(self, voc):
    self.voc = voc
    self.block = voc
    self.check(self.name not in voc.symbol_decls,
                f"duplicate declaration in vocabulary: {self.name}")
    voc.symbol_decls[self.name] = self
    for s in self.sorts:
        s.annotate(voc, {})
    self.out.annotate(voc, {})
    for c in self.constructors:
        c.type = self.name
        self.check(c.name not in voc.symbol_decls or self.name == CONCEPT,
                    f"duplicate '{c.name}' constructor for '{self.name}' type")
        voc.symbol_decls[c.name] = c
    if self.interpretation:
        self.interpretation.annotate(voc)
TypeDeclaration.annotate = annotate


# Class SymbolDeclaration  #######################################################

def annotate(self, voc):
    self.voc = voc
    self.check(self.name is not None, "Internal error")
    self.check(self.name not in voc.symbol_decls,
                f"duplicate declaration in vocabulary: {self.name}")
    voc.symbol_decls[self.name] = self
    for s in self.sorts:
        s.annotate(voc, {})
    self.out.annotate(voc, {})
    self.type = self.out.name

    for s in chain(self.sorts, [self.out]):
        self.check(s.name != CONCEPT or s == s, # use equality to check nested concepts
                   f"`Concept` must be qualified with a type signature in {self}")
    self.base_type = (None if self.out.name != BOOL or self.arity != 1 else
                      self.sorts[0].decl.base_type)
    return self
SymbolDeclaration.annotate = annotate


# Class VarDeclaration  #######################################################

def annotate(self, voc):
    self.check(self.name not in voc.symbol_decls,
                f"duplicate declaration in vocabulary: {self.name}")
    self.check(self.name == self.name.rstrip(string.digits),
                f"Variable {self.name} cannot be declared with a digital suffix.")
    voc.symbol_decls[self.name] = self
    self.subtype.annotate(voc, {})
    return self
VarDeclaration.annotate = annotate


# Class Symbol  #######################################################

def annotate(self, voc, q_vars):
    if self.name in q_vars:
        return q_vars[self.name]

    self.check(self.name in voc.symbol_decls,
               f'Undeclared symbol name: "{self.name}"')

    self.decl = voc.symbol_decls[self.name]
    self.type = self.decl.type
    return self
Symbol.annotate = annotate


# Class Type  #######################################################

def annotate(self, voc, q_vars):
    Symbol.annotate(self, voc, q_vars)
    if self.out:
        self.ins = [s.annotate(voc, q_vars) for s in self.ins]
        self.out = self.out.annotate(voc, q_vars)
    return self
Type.annotate = annotate


# Class TheoryBlock  #######################################################

def annotate(self, idp):
    self.check(self.vocab_name in idp.vocabularies,
                f"Unknown vocabulary: {self.vocab_name}")
    self.voc = idp.vocabularies[self.vocab_name]

    for i in self.interpretations.values():
        i.annotate(self)
    self.voc.add_voc_to_block(self)

    self.definitions = [e.annotate(self.voc, {}) for e in self.definitions]

    self.constraints = OrderedSet([e.annotate(self.voc, {})
                                    for e in self.constraints])
TheoryBlock.annotate = annotate


# Class Definition  #######################################################

def annotate(self: Definition, voc, q_vars):
    self.rules = [r.annotate(voc, q_vars) for r in self.rules]

    # create level-mapping symbols, as needed
    # self.level_symbols: dict[SymbolDeclaration, Symbol]
    dependencies = set()
    for r in self.rules:
        symbs: dict[str, Symbol] = {}
        r.body.collect_symbols(symbs)
        for s in symbs.values():
            dependencies.add((r.definiendum.symbol.decl, s))

    while True:
        new_relations = set((x, w) for x, y in dependencies
                            for q, w in dependencies if q == y)
        closure_until_now = dependencies | new_relations
        if len(closure_until_now) == len(dependencies):
            break
        dependencies = closure_until_now

    # check for nested recursive symbols
    symbs = {s for (s, ss) in dependencies if s == ss}
    nested: set[SymbolDeclaration] = set()
    for r in self.rules:
        decl = r.definiendum.symbol.decl
        r.body.collect_nested_symbols(nested, False)
        if decl in symbs and decl not in self.inductive:
            self.inductive.add(decl)

    if self.mode == Semantics.RECDATA:
        # check that the variables in r.out are in the arguments of definiendum
        for r in self.rules:
            if r.out:
                args = set()
                for e in r.definiendum.sub_exprs:
                    for v in e.variables:
                        args.add(v)
                error = list(set(r.out.variables) - args)
                self.check(len(error) == 0,
                        f"Eliminate variable {error} in the head of : {r}")

    # check for nested recursive symbols
    nested = set()
    for r in self.rules:
        r.body.collect_nested_symbols(nested, False)
    for decl in self.inductive:
        self.check(decl not in nested,
                    f"Inductively defined nested symbols are not supported yet: "
                    f"{decl.name}.")
        if self.mode != Semantics.RECDATA:
            self.check(decl.out.name == BOOL,
                        f"Inductively defined functions are not supported yet: "
                        f"{decl.name}.")

    # create common variables, and rename vars in rule
    self.canonicals = {}
    for r in self.rules:
        # create common variables
        decl = voc.symbol_decls[r.definiendum.decl.name]
        if decl.name not in self.def_vars:
            name = f"{decl.name}_"
            q_v = {f"{decl.name}{str(i)}_":
                    VARIABLE(f"{decl.name}{str(i)}_", sort)
                    for i, sort in enumerate(decl.sorts)}
            if decl.out.name != BOOL:
                q_v[name] = VARIABLE(name, decl.out)
            self.def_vars[decl.name] = q_v

        # rename the variables in the arguments of the definiendum
        new_vars_dict = self.def_vars[decl.name]
        new_vars = list(new_vars_dict.values())
        renamed = deepcopy(r)

        vars = {var.name : var for q in renamed.quantees for vars in q.vars for var in vars}
        args = renamed.definiendum.sub_exprs + ([renamed.out] if r.out else [])
        r.check(len(args) == len(new_vars), "Internal error")

        for i in range(len(args)- (1 if r.out else 0)):  # without rule.out
            arg, nv = renamed.definiendum.sub_exprs[i], new_vars[i]
            if type(arg) == Variable \
            and arg.name in vars and arg.name not in new_vars_dict:  # a variable, but not repeated (and not a new variable name, by chance)
                del vars[arg.name]
                rename_args(renamed, {arg.name: nv})
            else:
                eq = EQUALS([nv, arg])
                renamed.body = AND([eq, renamed.body])

        canonical = deepcopy(renamed)

        for v in vars.values():
            renamed.body = EXISTS([Quantee.make(v, sort=v.sort).annotate(voc, {})],
                                  renamed.body)
        self.renamed.setdefault(decl, []).append(renamed)

        # rename the variable for the value of the definiendum
        if r.out:  # now process r.out
            arg, nv = canonical.out, new_vars[-1]
            if type(arg) == Variable \
            and arg.name in vars and arg.name not in new_vars:  # a variable, but not repeated (and not a new variable name, by chance)
                del vars[arg.name]
                rename_args(canonical, {arg.name: nv})
            else:
                eq = EQUALS([nv, arg])
                canonical.body = AND([eq, canonical.body])

        for v in vars.values():
            canonical.body = EXISTS([Quantee.make(v, sort=v.sort).annotate(voc, {})],
                                    canonical.body)

        canonical.definiendum.sub_exprs = new_vars[:-1] if r.out else new_vars
        canonical.out = new_vars[-1] if r.out else None
        canonical.quantees = [Quantee.make(v, sort=v.sort) for v in new_vars]

        self.canonicals.setdefault(decl, []).append(canonical)

    # join the bodies of rules
    for decl, rules in self.canonicals.items():
        new_rule = copy(rules[0])
        exprs = [rule.body for rule in rules]
        new_rule.body = OR(exprs)
        self.clarks[decl] = new_rule
    return self
Definition.annotate = annotate


# Class Rule  #######################################################

def annotate(self, voc, q_vars):
    self.original = copy(self)
    self.check(not self.definiendum.symbol.is_intentional(),
                f"No support for intentional objects in the head of a rule: "
                f"{self}")
    # create head variables
    q_v = copy(q_vars)
    for q in self.quantees:
        q.annotate(voc, q_vars)
        for vars in q.vars:
            for var in vars:
                var.sort = q.sub_exprs[0] if q.sub_exprs else None
                q_v[var.name] = var

    self.definiendum = self.definiendum.annotate(voc, q_v)
    self.body = self.body.annotate(voc, q_v)
    if self.out:
        self.out = self.out.annotate(voc, q_v)

    return self
Rule.annotate = annotate

def rename_args(self: Rule, subs: dict[str, Expression]):
    """replace old variables by new variables
        (ignoring arguments in the head before the it
    """
    self.body = self.body.interpret(None, subs)
    self.out = (self.out.interpret(None, subs) if self.out else
                self.out)
    args = self.definiendum.sub_exprs
    for j in range(0, len(args)):
        args[j] = args[j].interpret(None, subs)


# Class Structure  #######################################################

def annotate(self, idp):
    """
    Annotates the structure with the enumerations found in it.
    Every enumeration is converted into an assignment, which is added to
    `self.assignments`.

    :arg idp: a `Parse.IDP` object.
    :returns None:
    """
    self.check(self.vocab_name in idp.vocabularies,
               f"Unknown vocabulary: {self.vocab_name}")
    self.voc = idp.vocabularies[self.vocab_name]
    for i in self.interpretations.values():
        i.annotate(self)
    self.voc.add_voc_to_block(self)
Structure.annotate = annotate


# Class SymbolInterpretation  #######################################################

def annotate(self, block):
    """
    Annotate the symbol.

    :arg block: a Structure object
    :returns None:
    """
    voc = block.voc
    self.block = block
    self.symbol = SYMBOL(self.name).annotate(voc, {})
    enumeration = self.enumeration  # shorthand

    # create constructors if it is a type enumeration
    self.is_type_enumeration = (type(self.symbol.decl) != SymbolDeclaration)
    if self.is_type_enumeration and enumeration.constructors:
        # create Constructors before annotating the tuples
        for c in enumeration.constructors:
            c.type = self.name
            self.check(c.name not in voc.symbol_decls,
                    f"duplicate '{c.name}' constructor for '{self.name}' symbol")
            voc.symbol_decls[c.name] = c  #TODO risk of side-effects => use local decls ? issue #81

    enumeration.annotate(voc)

    self.check(self.is_type_enumeration
                or all(s.name not in [INT, REAL, DATE]  # finite domain #TODO
                        for s in self.symbol.decl.sorts)
                or self.default is None,
        f"Can't use default value for '{self.name}' on infinite domain nor for type enumeration.")

    self.check(not(self.symbol.decl.out.decl.base_type.name == BOOL
                   and type(enumeration) == FunctionEnum),
        f"Can't use function enumeration for predicates '{self.name}' (yet)")

    # predicate enumeration have FALSE default
    if type(enumeration) != FunctionEnum and self.default is None:
        self.default = FALSE

    if self.default is not None:
        self.default = self.default.annotate(voc, {})
        self.check(self.default.is_value(),
                   f"Value for '{self.name}' may only use numerals,"
                   f" identifiers or constructors: '{self.default}'")
SymbolInterpretation.annotate = annotate


# Class Enumeration  #######################################################

def annotate(self, voc):
    if self.tuples:
        for t in self.tuples:
            t.annotate(voc)
Enumeration.annotate = annotate


# Class TupleIDP  #######################################################

def annotate(self, voc):
    self.args = [arg.annotate(voc, {}) for arg in self.args]
    self.check(all(a.is_value() for a in self.args),
               f"Interpretation may only contain numerals,"
               f" identifiers or constructors: '{self}'")
TupleIDP.annotate = annotate


# Class ConstructedFrom  #######################################################

def annotate(self, voc):
    for c in self.constructors:
        for i, ts in enumerate(c.sorts):
            if ts.accessor is None:
                ts.accessor = SYMBOL(f"{c.name}_{i}")
            if ts.accessor.name in self.accessors:
                self.check(self.accessors[ts.accessor.name] == i,
                           "Accessors used at incompatible indices")
            else:
                self.accessors[ts.accessor.name] = i
        c.annotate(voc)
ConstructedFrom.annotate = annotate


# Class Constructor  #######################################################

def annotate(self, voc):
    for a in self.sorts:
        self.check(a.type in voc.symbol_decls,
                   f"Unknown type: {a.type}" )
        a.decl = SymbolDeclaration(annotations='', name=a.accessor,
                                   sorts=[TYPE(self.type)],
                                   out=TYPE(a.type))
        a.decl.annotate(voc)
    self.tester = SymbolDeclaration(annotations='',
                                    name=SYMBOL(f"is_{self.name}"),
                                    sorts=[TYPE(self.type)],
                                    out=TYPE(BOOL))
    self.tester.annotate(voc)
Constructor.annotate = annotate


# Class Display  #######################################################

def annotate(self, idp):
    self.voc = idp.vocabulary

    # add display predicates

    viewType = TypeDeclaration(name='_ViewType',
        constructors=[CONSTRUCTOR('normal'),
                        CONSTRUCTOR('expanded')])
    viewType.annotate(self.voc)

    # Check the AST for any constructors that belong to open types.
    # For now, the only open types are `unit` and `heading`.
    open_constructors = {'unit': [], 'heading': []}
    for constraint in self.constraints:
        constraint.generate_constructors(open_constructors)

    # Next, we convert the list of constructors to actual types.
    open_types = {}
    for name, constructors in open_constructors.items():
        # If no constructors were found, then the type is not used.
        if not constructors:
            open_types[name] = None
            continue

        type_name = name.capitalize()  # e.g. type Unit (not unit)
        open_type = TypeDeclaration(name=type_name,
                                    constructors=constructors)
        open_type.annotate(self.voc)
        open_types[name] = SYMBOL(type_name)

    for name, out in [
        ('expand', SYMBOL(BOOL)),
        ('hide', SYMBOL(BOOL)),
        ('view', SYMBOL('_ViewType')),
        ('moveSymbols', SYMBOL(BOOL)),
        ('optionalPropagation', SYMBOL(BOOL)),
        ('manualPropagation', SYMBOL(BOOL)),
        ('optionalRelevance', SYMBOL(BOOL)),
        ('manualRelevance', SYMBOL(BOOL)),
        ('unit', open_types['unit']),
        ('heading', open_types['heading']),
        ('noOptimization', SYMBOL(BOOL))
    ]:
        symbol_decl = SymbolDeclaration(annotations='',
                                        name=SYMBOL(name),
                                        sorts=[], out=out)
        symbol_decl.annotate(self.voc)

    # annotate constraints and interpretations
    for constraint in self.constraints:
        constraint.annotate(self.voc, {})
    for i in self.interpretations.values():
        i.annotate(self)
Display.annotate = annotate


# Class Expression  #######################################################

def annotate(self, voc, q_vars):
    """annotate tree after parsing

    Resolve names and determine type as well as variables in the expression

    Args:
        voc (Vocabulary): the vocabulary
        q_vars (dict[str, Variable]): the quantifier variables that may appear in the expression

    Returns:
        Expression: an equivalent AST node, with updated type, .variables
    """
    self.sub_exprs = [e.annotate(voc, q_vars) for e in self.sub_exprs]
    return self.annotate1()
Expression.annotate = annotate


def annotate1(self):
    " annotations that are common to __init__ and make() "
    self.variables = set()
    for e in self.sub_exprs:
        self.variables.update(e.variables)
    return self
Expression.annotate1 = annotate1


# Class AIfExpr  #######################################################

def annotate1(self):
    self.type = self.sub_exprs[AIfExpr.THEN].type
    if not self.type:
        self.type = self.sub_exprs[AIfExpr.ELSE].type
    return Expression.annotate1(self)
AIfExpr.annotate1 = annotate1


# Class Quantee  #######################################################

def annotate(self, voc, q_vars):
    Expression.annotate(self, voc, q_vars)
    for vars in self.vars:
        self.check(not self.sub_exprs
                   or not self.sub_exprs[0].decl
                   or len(vars)==len(self.sub_exprs[0].decl.sorts),
                    f"Incorrect arity for {self}")
        for i, var in enumerate(vars):
            self.check(var.name not in voc.symbol_decls
                        or type(voc.symbol_decls[var.name]) == VarDeclaration,
                f"the quantified variable '{var.name}' cannot have"
                f" the same name as another symbol")
            var.sort = (self.sub_exprs[0].decl.sorts[i]
                        if self.sub_exprs and self.sub_exprs[0].decl
                        else None)
            var_decl = voc.symbol_decls.get(var.name.rstrip(string.digits), None)
            if self.subtype is None and var_decl:
                subtype = var_decl.subtype
                self.check(var.sort is None
                            or var.sort.name == subtype.name,
                    f"Can't use declared {var.name} as a "
                    f"{var.sort.name if var.sort else ''}")
                if var.sort is None:
                    self.sub_exprs = [subtype.annotate(voc, {})]
                    var.sort = self.sub_exprs[0]
            var.type = var.sort.decl.name if var.sort and var.sort.decl else ''
            q_vars[var.name] = var
    return self
Quantee.annotate = annotate


# Class AQuantification  #######################################################

def annotate(self, voc, q_vars):
    # also called by AAgregate.annotate
    q_v = copy(q_vars)
    for q in self.quantees:
        q.annotate(voc, q_v)
    self.sub_exprs = [e.annotate(voc, q_v) for e in self.sub_exprs]
    return self.annotate1()
AQuantification.annotate = annotate

def annotate1(self):
    Expression.annotate1(self)
    for q in self.quantees:  # remove declared variables
        for vs in q.vars:
            for v in vs:
                self.variables.discard(v.name)
    for q in self.quantees:  # add variables in sort expression
        for sort in q.sub_exprs:
            self.variables.update(sort.variables)
    return self
AQuantification.annotate1 = annotate1


# Class Operator  #######################################################

def annotate(self, voc, q_vars):
    self = Expression.annotate(self, voc, q_vars)

    for e in self.sub_exprs:
        if self.operator[0] in '&|∧∨⇒⇐⇔':
            self.check(e.type is None or e.type == BOOL or e.str in ['true', 'false'],
                       f"Expected boolean formula, got {e.type}: {e}")
    return self
Operator.annotate = annotate

def annotate1(self):
    if self.type is None:  # not a BOOL operator
        self.type = REAL if any(e.type == REAL for e in self.sub_exprs) \
                else INT if any(e.type == INT for e in self.sub_exprs) \
                else DATE if any(e.type == DATE for e in self.sub_exprs) \
                else self.sub_exprs[0].type  # constructed type, without arithmetic
    return Expression.annotate1(self)
Operator.annotate1 = annotate1


# Class AImplication  #######################################################

def annotate1(self):
    self.check(len(self.sub_exprs) == 2,
               "Implication is not associative.  Please use parenthesis.")
    self.type = BOOL
    return Expression.annotate1(self)
AImplication.annotate1 = annotate1


# Class AEquivalence  #######################################################

def annotate1(self):
    self.check(len(self.sub_exprs) == 2,
               "Equivalence is not associative.  Please use parenthesis.")
    self.type = BOOL
    return Expression.annotate1(self)
AEquivalence.annotate1 = annotate1

# Class ARImplication  #######################################################

def annotate(self, voc, q_vars):
    # reverse the implication
    self.sub_exprs = [e.annotate(voc, q_vars) for e in self.sub_exprs]
    out = AImplication.make(ops=['⇒'], operands=list(reversed(list(self.sub_exprs))),
                        annotations=None, parent=self)
    out.original = self
    return out.annotate(voc, q_vars)
ARImplication.annotate = annotate


# Class AComparison  #######################################################

def annotate(self, voc, q_vars):
    out = Operator.annotate(self, voc, q_vars)
    out.type = BOOL

    for e in self.sub_exprs:
        if self.operator[0] in "<>≤≥":
            decl = voc.symbol_decls.get(e.type, None)
            self.check(e.type != BOOL,
                        f"Expected numeric formula, got {e.type}: {e}")
            self.check(e.type is None or e.type in ['', INT, REAL, DATE]
                       or decl.type in [INT, REAL, DATE]
                       or (hasattr(decl, 'interpretation')
                           and decl.interpretation is None)
                       or not hasattr(decl, 'enumeration')
                       or decl.enumeration is None,
                        f"Expected numeric formula, got {e.type}: {e}")

    # a≠b --> Not(a=b)
    if len(self.sub_exprs) == 2 and self.operator == ['≠']:
        out = NOT(EQUALS(self.sub_exprs))
    return out
AComparison.annotate = annotate


# Class AUnary  #######################################################

def annotate1(self):
    if len(self.operators) % 2 == 0: # negation of negation
        return self.sub_exprs[0]
    self.type = self.sub_exprs[0].type
    return Expression.annotate1(self)
AUnary.annotate1 = annotate1


# Class AAggregate  #######################################################

def annotate(self, voc, q_vars):
    if not self.annotated:

        self = AQuantification.annotate(self, voc, q_vars)

        if self.aggtype == "sum" and len(self.sub_exprs) == 2:
            self.original = copy(self)
            self.sub_exprs = [AIfExpr(self.parent, self.sub_exprs[1],
                                    self.sub_exprs[0], ZERO).annotate1()]

        if self.aggtype == "#":
            self.sub_exprs = [IF(self.sub_exprs[0], Number(number='1'),
                                 Number(number='0'))]
            self.type = INT
        else:
            self.type = self.sub_exprs[0].type
            if self.aggtype in ["min", "max"]:
                # the `min` aggregate in `!y in T: min(lamda x in type: term(x,y) if cond(x,y))=0`
                # is replaced by `_*(y)` with the following co-constraint:
                #     !y in T: ( ?x in type: cond(x,y) & term(x) = _*(y)
                #                !x in type: cond(x,y) => term(x) =< _*(y).
                self.check(self.type, f"Can't infer type of {self}")
                name = "_" + self.str
                if name in voc.symbol_decls:
                    symbol_decl = voc.symbol_decls[name]
                    to_create = False
                else:
                    symbol_decl = SymbolDeclaration.make(
                        "_"+self.str, # name `_ *`
                        len(q_vars),  # arity
                        [TYPE(v.sort.code) for v in q_vars.values()],
                        TYPE(self.type)).annotate(voc)    # output_domain
                    to_create = True
                symbol = SYMBOL(symbol_decl.name)
                applied = AppliedSymbol.make(symbol, q_vars.values())
                applied = applied.annotate(voc, q_vars)

                if to_create:
                    eq = EQUALS([deepcopy(applied), self.sub_exprs[0]])
                    if len(self.sub_exprs) == 2:
                        eq = AND([self.sub_exprs[1], eq])
                    coc1 = EXISTS(self.quantees, eq)

                    op = '≤' if self.aggtype == "min" else '≥'
                    comp = AComparison.make(op,
                                    deepcopy([applied, self.sub_exprs[0]]))
                    if len(self.sub_exprs) == 2:
                        comp = IMPLIES([self.sub_exprs[1], comp])
                    coc2 = FORALL(deepcopy(self.quantees), comp)

                    coc = AND([coc1, coc2])
                    quantees = [Quantee.make(v, sort=v.sort).annotate(voc, {})
                                for v in q_vars.values()]
                    applied.co_constraint = (
                        coc if not quantees else
                        FORALL(quantees, coc).annotate(voc, q_vars))
                    applied.co_constraint.annotations['reading'] = f"Calculation of {self.code}"
                return applied
        self.annotated = True
    return self
AAggregate.annotate = annotate
AAggregate.annotate1 = AQuantification.annotate1


# Class AppliedSymbol  #######################################################

def annotate(self, voc, q_vars):
    self.symbol = self.symbol.annotate(voc, q_vars)
    if self.symbol.decl:
        self.check(self.symbol.decl.arity == len(self.sub_exprs)
                   or self.symbol.decl.name in ['hide', 'unit', 'heading', 'noOptimization'],
            f"Incorrect number of arguments in {self}: "
            f"should be {self.symbol.decl.arity}")
    self.check((not self.symbol.decl or type(self.symbol.decl) != Constructor
                or 0 < self.symbol.decl.arity),
               f"Constructor `{self.symbol}` cannot be applied to argument(s)")
    self.sub_exprs = [e.annotate(voc, q_vars) for e in self.sub_exprs]
    if self.in_enumeration:
        self.in_enumeration.annotate(voc)
    out = self.annotate1()

    # move the negation out
    if 'not' in self.is_enumerated:
        out = AppliedSymbol.make(out.symbol, out.sub_exprs,
                                 is_enumerated='is enumerated')
        out = NOT(out)
    elif 'not' in self.is_enumeration:
        out = AppliedSymbol.make(out.symbol, out.sub_exprs,
                                 is_enumeration='in',
                                 in_enumeration=out.in_enumeration)
        out = NOT(out)
    return out
AppliedSymbol.annotate = annotate

def annotate1(self):
    out = Expression.annotate1(self)
    out.symbol = out.symbol.annotate1()
    out.variables.update(out.symbol.variables)
    return out.simplify1()
AppliedSymbol.annotate1 = annotate1


# Class SymbolExpr  #######################################################

def annotate(self, voc, q_vars):
    out = Expression.annotate(self, voc, q_vars)
    return out.simplify1()
SymbolExpr.annotate = annotate


# Class Variable  #######################################################

def annotate(self, voc, q_vars):
    self.type = self.sort.decl.name if self.sort and self.sort.decl else ''
    return self
Variable.annotate = annotate


# Class Number  #######################################################

def annotate(self, voc, q_vars):
    self.decl = voc.symbol_decls[self.type]
    return self
Number.annotate = annotate


# Class UnappliedSymbol  #######################################################

def annotate(self, voc, q_vars):
    if self.name in q_vars:  # ignore VarDeclaration
        return q_vars[self.name]
    if self.name in voc.symbol_decls:
        self.decl = voc.symbol_decls[self.name]
        self.variables = {}
        self.check(type(self.decl) == Constructor,
                   f"{self} should be applied to arguments (or prefixed with a back-tick)")
        return self
    # elif self.name in voc.symbol_decls:  # in symbol_decls
    #     out = AppliedSymbol.make(self.s, self.sub_exprs)
    #     return out.annotate(voc, q_vars)
    # If this code is reached, an undefined symbol was present.
    if self.name.rstrip(string.digits) in q_vars:  # after considering it as a declared symbol
        return self
    self.check(False, f"Symbol not in vocabulary: {self}")
UnappliedSymbol.annotate = annotate


# Class Brackets  #######################################################

def annotate1(self):
    if not self.annotations:
        return self.sub_exprs[0]  # remove the bracket
    self.type = self.sub_exprs[0].type
    if self.annotations['reading']:
        self.sub_exprs[0].annotations = self.annotations
    self.variables = self.sub_exprs[0].variables
    return self
Brackets.annotate1 = annotate1


Done = True
