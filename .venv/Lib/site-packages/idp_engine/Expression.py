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

This module contains the ASTNode classes for expressions.

(Many methods are monkey-patched by other modules)

"""
from __future__ import annotations

from copy import copy, deepcopy
from collections import ChainMap
from datetime import date
from dateutil.relativedelta import *
from fractions import Fraction
from re import findall
from sys import intern
from textx import get_location
from typing import (Optional, List, Union, Tuple, Set, Callable, TYPE_CHECKING,
                    Generator, Any)
if TYPE_CHECKING:
    from .Theory import Theory
    from .Assignments import Assignments, Status
    from .Parse import SymbolDeclaration, SymbolInterpretation, Enumeration

from .utils import (unquote, OrderedSet, BOOL, INT, REAL, DATE, CONCEPT,
                    RESERVED_SYMBOLS, IDPZ3Error, Semantics)


class ASTNode(object):
    """superclass of all AST nodes
    """

    def check(self, condition: bool, msg: str):
        """raises an exception if `condition` is not True

        Args:
            condition (Bool): condition to be satisfied
            msg (str): error message

        Raises:
            IDPZ3Error: when `condition` is not met
        """
        if not condition:
            try:
                location = get_location(self)
            except:
                raise IDPZ3Error(f"{msg}")
            line = location['line']
            col = location['col']
            raise IDPZ3Error(f"Error on line {line}, col {col}: {msg}")

    def dedup_nodes(self,
                    kwargs: dict[str, List[ASTNode]],
                    arg_name:str
                    ) -> dict[str, ASTNode]:
        """pops `arg_name` from kwargs as a list of named items
        and returns a mapping from name to items

        Args:
            kwargs: dictionary mapping named arguments to list of ASTNodes

            arg_name: name of the kwargs argument, e.g. "interpretations"

        Returns:
            dict[str, ASTNode]: mapping from `name` to AST nodes

        Raises:
            AssertionError: in case of duplicate name
        """
        ast_nodes = kwargs.pop(arg_name)
        out = {}
        for i in ast_nodes:
            # can't get location here
            assert hasattr(i, "name"), "internal error"
            assert i.name not in out, f"Duplicate '{i.name}' in {arg_name}"
            out[i.name] = i
        return out

    def annotate(self, idp):
        return  # monkey-patched

    def annotate1(self):
        return  # monkey-patched

    def interpret(self, problem: Optional[Theory]) -> ASTNode:
        return self  # monkey-patched

    def EN(self):
        pass  # monkey-patched


def catch_error(func):
    def inner_function(self, *args, **kwargs):
        try:
            return func(self, *args, **kwargs)
        except IDPZ3Error as e:
            raise e
        except Exception as e:
            self.check(False, str(e))
    return inner_function


class Annotations(ASTNode):
    def __init__(self, parent, annotations: List[str]):

        self.annotations : dict[str, Union[str, dict[str, Any]]] = {}
        v: Union[str, dict[str, Any]]
        for s in annotations:
            p = s.split(':', 1)
            if len(p) == 2:
                if p[0] != 'slider':
                    k, v = (p[0], p[1])
                else:
                    # slider:(lower_sym, upper_sym) in (lower_bound, upper_bound)
                    pat = r"\(((.*?), (.*?))\)"
                    arg = findall(pat, p[1])
                    l_symb = arg[0][1]
                    u_symb = arg[0][2]
                    l_bound = arg[1][1]
                    u_bound = arg[1][2]
                    slider_arg = {'lower_symbol': l_symb,
                                'upper_symbol': u_symb,
                                'lower_bound': l_bound,
                                'upper_bound': u_bound}
                    k, v = ('slider', slider_arg)
            else:
                k, v = ('reading', p[0])
            self.check(k not in self.annotations,
                       f"Duplicate annotation: [{k}: {v}]")
            self.annotations[k] = v


class Constructor(ASTNode):
    """Constructor declaration

    Attributes:
        name (string): name of the constructor

        sorts (List[Symbol]): types of the arguments of the constructor

        type (string): name of the type that contains this constructor

        arity (Int): number of arguments of the constructor

        tester (SymbolDeclaration): function to test if the constructor
        has been applied to some arguments (e.g., is_rgb)

        symbol (Symbol): only for Symbol constructors

        range: the list of identifiers
    """

    def __init__(self, parent,
                 name: Union[UnappliedSymbol, str],
                 args: Optional[List[Accessor]] = None):
        self.name : str = (name.s.name if type(name) == UnappliedSymbol else
                     name)
        self.sorts = args if args is not None else []

        self.arity = len(self.sorts)

        self.type = None
        self.symbol = None
        self.tester = None
        self.range: Optional[List[Expression]] = None

    def __str__(self):
        return (self.name if not self.sorts else
                f"{self.name}({', '.join((str(a) for a in self.sorts))})" )

def CONSTRUCTOR(name: str, args=None) -> Constructor:
    return Constructor(None, name, args)


class Accessor(ASTNode):
    """represents an accessor and a type

    Attributes:
        accessor (UnappliedSymbol, Optional): name of accessor function

        type (string): name of the output type of the accessor

        decl (SymbolDeclaration): declaration of the accessor function
    """
    def __init__(self, parent,
                 type: UnappliedSymbol,
                 accessor: Optional[UnappliedSymbol] = None):
        self.accessor = accessor
        self.type = type.name
        self.decl: Optional[SymbolDeclaration] = None

    def __str__(self):
        return (self.type if not self.accessor else
                f"{self.accessor}: {self.type}" )


class Expression(ASTNode):
    """The abstract class of AST nodes representing (sub-)expressions.

    Attributes:
        code (string):
            Textual representation of the expression.  Often used as a key.

            It is generated from the sub-tree.
            Some tree transformations change it (e.g., interpret),
            others don't.

        sub_exprs (List[Expression]):
            The children of the AST node.

            The list may be reduced by simplification.

        type (string):
            The name of the type of the expression, e.g., ``bool``.

        co_constraint (Expression, optional):
            A constraint attached to the node.

            For example, the co_constraint of ``square(length(top()))`` is
            ``square(length(top())) = length(top())*length(top()).``,
            assuming ``square`` is appropriately defined.

            The co_constraint of a defined symbol applied to arguments
            is the instantiation of the definition for those arguments.
            This is useful for definitions over infinite domains,
            as well as to compute relevant questions.

        annotations (dict[str, str]):
            The set of annotations given by the expert in the IDP-Z3 program.

            ``annotations['reading']`` is the annotation
            giving the intended meaning of the expression (in English).

        original (Expression):
            The original expression, before propagation and simplification.

        variables (Set(string)):
            The set of names of the variables in the expression, before interpretation.

        is_type_constraint_for (string):
            name of the symbol for which the expression is a type constraint

    """
    # slots for marginally faster code
    __slots__ = ('sub_exprs', 'code',
                 'annotations', 'original', 'str', 'variables', 'type',
                 'is_type_constraint_for', 'co_constraint',
                 'questions', 'relevant')

    def __init__(self, parent=None):
        if parent:
            self.parent = parent
        self.sub_exprs: List[Expression]

        self.code: str = intern(str(self))
        if not hasattr(self, 'annotations') or self.annotations == None:
            self.annotations: dict[str, str] = {'reading': self.code}
        elif type(self.annotations) == Annotations:
            self.annotations = self.annotations.annotations
        self.original: Expression = self

        self.str: str = self.code
        self.variables: Optional[Set[str]] = None
        self.type: Optional[str] = None
        self.is_type_constraint_for: Optional[str] = None
        self.co_constraint: Optional[Expression] = None

        # attributes of the top node of a (co-)constraint
        self.questions: Optional[OrderedSet] = None
        self.relevant: Optional[bool] = None

    def __deepcopy__(self, memo):
        """ copies everyting but .original """
        key = str(self)
        val = memo.get(key, None)
        if val is not None:
            return val
        if self.is_value():
            return self
        out = copy(self)
        out.sub_exprs = [deepcopy(e, memo) for e in out.sub_exprs]
        out.variables = deepcopy(out.variables, memo)
        out.co_constraint = deepcopy(out.co_constraint, memo)
        out.questions = deepcopy(self.questions, memo)
        memo[key] = out
        return out

    def same_as(self, other: Expression):
        # symmetric
        if self.str == other.str: # and type(self) == type(other):
            return True

        if (type(self) in [Number, Date]
        and type(other) in [Number, Date]):
            return float(self.py_value) == float(other.py_value)

        return False

    def __repr__(self): return str(self)

    def __log__(self):  # for debugWithYamlLog
        return {'class': type(self).__name__,
                'code': self.code,
                'str': self.str,
                'co_constraint': self.co_constraint}

    def has_variables(self) -> bool:
        return any(e.has_variables() for e in self.sub_exprs)

    def collect(self,
                questions: OrderedSet,
                all_: bool=True,
                co_constraints: bool=True
                ):
        """collects the questions in self.

        `questions` is an OrderedSet of Expression
        Questions are the terms and the simplest sub-formula that
        can be evaluated.

        all_=False : ignore expanded formulas
        and AppliedSymbol interpreted in a structure

        co_constraints=False : ignore co_constraints

        default implementation for UnappliedSymbol, AIfExpr, AUnary, Variable,
        Number_constant, Brackets
        """
        for e in self.sub_exprs:
            e.collect(questions, all_, co_constraints)

    def collect_symbols(self,
                        symbols: Optional[dict[str, SymbolDeclaration]] = None,
                        co_constraints: bool=True
                        ) -> dict[str, SymbolDeclaration]:
        """ returns the list of symbol declarations in self, ignoring type constraints
        """
        symbols = {} if symbols == None else symbols
        assert symbols is not None, "Internal error"
        if self.is_type_constraint_for is None:  # ignore type constraints
            if (hasattr(self, 'decl') and self.decl
                and self.decl.__class__.__name__ == "SymbolDeclaration"
                and not self.decl.name in RESERVED_SYMBOLS):
                symbols[self.decl.name] = self.decl
            for e in self.sub_exprs:
                e.collect_symbols(symbols, co_constraints)
        return symbols

    def collect_nested_symbols(self,
                               symbols: Set[SymbolDeclaration],
                               is_nested: bool
                               ) -> Set[SymbolDeclaration]:
        return self  # monkey-patched

    def generate_constructors(self, constructors: dict[str, List[Constructor]]):
        """ fills the list `constructors` with all constructors belonging to
        open types.
        """
        for e in self.sub_exprs:
            e.generate_constructors(constructors)

    def collect_co_constraints(self, co_constraints: OrderedSet, recursive=True):
        """ collects the constraints attached to AST nodes, e.g. instantiated
        definitions

        Args:
            recursive: if True, collect co_constraints of co_constraints too
        """
        if self.co_constraint is not None and self.co_constraint not in co_constraints:
            co_constraints.append(self.co_constraint)
            if recursive:
                self.co_constraint.collect_co_constraints(co_constraints, recursive)
        for e in self.sub_exprs:
            e.collect_co_constraints(co_constraints, recursive)

    def is_value(self) -> bool:
        """True for numerals, date, identifiers,
        and constructors applied to values.

        Synomym: "is ground", "is rigid"

        Returns:
            bool: True if `self` represents a value.
        """
        return False

    def is_reified(self) -> bool:
        """False for values and for symbols applied to values.

        Returns:
            bool: True if `self` has to be reified to obtain its value in a Z3 model.
        """
        return True

    def is_assignment(self) -> bool:
        """

        Returns:
            bool: True if `self` assigns a rigid term to a rigid function application
        """
        return False

    def has_decision(self) -> bool:
        # returns true if it contains a variable declared in decision
        # vocabulary
        return any(e.has_decision() for e in self.sub_exprs)

    def type_inference(self) -> dict[str, Symbol]:
        # returns a dictionary {Variable : Symbol}
        try:
            return dict(ChainMap(*(e.type_inference() for e in self.sub_exprs)))
        except AttributeError as e:
            if "has no attribute 'sorts'" in str(e):
                msg = f"Incorrect arity for {self}"
            else:
                msg = f"Unknown error for {self}"
            self.check(False, msg)
            return {}  # dead code

    def __str__(self) -> str:
        return ''  # monkey-patched

    def _change(self: Expression,
                sub_exprs: Optional[List[Expression]] = None,
                ops : Optional[List[str]] = None,
                simpler : Optional[Expression] = None,
                co_constraint : Optional[Expression] = None
                ) -> Expression:
        return self  # monkey-patched

    def update_exprs(self, new_exprs: Generator[Expression, None, None]) -> Expression:
        return self  # monkey-patched

    def simplify1(self) -> Expression:
        return self  # monkey-patched

    def interpret(self,
                  problem: Optional[Theory],
                  subs: dict[str, Expression]
                  ) -> Expression:
        return self  # monkey-patched

    def _interpret(self,
                    problem: Optional[Theory],
                    subs: dict[str, Expression]
                    ) -> Expression:
        return self  # monkey-patched

    def substitute(self,
                   e0: Expression,
                   e1: Expression,
                   assignments: Assignments,
                   tag=None) -> Expression:
        return self  # monkey-patched

    def simplify_with(self, assignments: Assignments, co_constraints_too=True) -> Expression:
        return self  # monkey-patched

    def symbolic_propagate(self,
                           assignments: Assignments,
                           tag: Status,
                           truth: Optional[Expression] = None
                           ):
        return  # monkey-patched

    def propagate1(self,
                   assignments: Assignments,
                   tag: Status,
                   truth: Optional[Expression] = None
                   ):
        return  # monkey-patched

    def translate(self, problem: Theory, vars={}):
        pass  # monkey-patched

    def reified(self, problem: Theory):
        pass  # monkey-patched

    def translate1(self, problem: Theory, vars={}):
        pass  # monkey-patched

    def as_set_condition(self) -> Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]:
        """Returns an equivalent expression of the type "x in y", or None

        Returns:
            Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]: meaning "expr is (not) in enumeration"
        """
        return (None, None, None)

    def split_equivalences(self) -> Expression:
        """Returns an equivalent expression where equivalences are replaced by
        implications

        Returns:
            Expression
        """
        out = self.update_exprs(e.split_equivalences() for e in self.sub_exprs)
        return out

    def add_level_mapping(self,
                          level_symbols: dict[SymbolDeclaration, Symbol],
                          head: AppliedSymbol,
                          pos_justification: bool,
                          polarity: bool,
                          mode: Semantics
                          ) -> Expression:
        return self  # monkey-patched


class Symbol(Expression):
    """Represents a Symbol.  Handles synonyms.

    Attributes:
        name (string): name of the symbol
    """
    TO = {'Bool': BOOL, 'Int': INT, 'Real': REAL,
          '`Bool': '`'+BOOL, '`Int': '`'+INT, '`Real': '`'+REAL,}

    def __init__(self, parent, name: str):
        self.name = unquote(name)
        self.name = Symbol.TO.get(self.name, self.name)
        self.sub_exprs = []
        self.decl: Optional[SymbolDeclaration] = None
        super().__init__()
        self.variables = set()

    def __str__(self):
        return self.name

    def __repr__(self):
        return str(self)

    def is_value(self): return True

    def has_element(self, term: Expression,
                    interpretations: dict[str, SymbolInterpretation],
                    extensions: dict[str, Extension]
                    ) -> Expression:
        """Returns an expression that says whether `term` is in the type/predicate denoted by `self`.

        Args:
            term (Expression): the argument to be checked

        Returns:
            Expression: whether `term` is in the type denoted by `self`.
        """
        assert self.decl is not None, "Internal error"
        self.check(self.decl.out.name == BOOL, "internal error")
        return self.decl.contains_element(term, interpretations, extensions)

def SYMBOL(name: str) -> Symbol:
    return Symbol(None, name)


class Type(Symbol):
    """ASTNode representing `aType` or `Concept[aSignature]`, e.g., `Concept[T*T->Bool]`

    Inherits from Symbol

    Args:
        name (Symbol): name of the concept

        ins (List[Symbol], Optional): domain of the Concept signature, e.g., `[T, T]`

        out (Symbol, Optional): range of the Concept signature, e.g., `Bool`
    """

    def __init__(self, parent,
                 name:str,
                 ins: Optional[List[Type]] = None,
                 out: Optional[Type] = None):
        self.ins = ins
        self.out = out
        super().__init__(parent, name)

    def __str__(self):
        return self.name + ("" if not self.out else
                            f"[{'*'.join(str(s) for s in self.ins)}->{self.out}]")

    def __eq__(self, other):
        self.check(self.name != CONCEPT or self.out,
                   f"`Concept` must be qualified with a type signature")
        return (self.name == other.name and
                (not self.out or (
                    self.out == other.out and
                    len(self.ins) == len(other.ins) and
                    all(s==o for s, o in zip(self.ins, other.ins)))))

    def extension(self,
                  interpretations: dict[str, SymbolInterpretation],
                  extensions: dict[str, Extension]
                  ) -> Extension:
        return extensions[""]  # monkey-patched

    def has_element(self,
                    term: Expression,
                    interpretations: dict[str, SymbolInterpretation],
                    extensions: dict[str, Extension]
                    ) -> Expression:
        """Returns an Expression that says whether `term` is in the type/predicate denoted by `self`.

        Args:
            term (Expression): the argument to be checked

        Returns:
            Expression: whether `term` `term` is in the type denoted by `self`.
        """
        if self.name == CONCEPT:
            extension = self.extension(interpretations, extensions)[0]
            assert extension is not None, "Internal error"
            comparisons = [EQUALS([term, c[0]]) for c in extension]
            return OR(comparisons)
        else:
            assert self.decl is not None, "Internal error"
            self.check(self.decl.out.name == BOOL, "internal error")
            return self.decl.contains_element(term, interpretations, extensions)

def TYPE(name: str, ins=None, out=None) -> Type:
    return Type(None, name, ins, out)


class AIfExpr(Expression):
    PRECEDENCE = 10
    IF = 0
    THEN = 1
    ELSE = 2

    def __init__(self, parent,
                 if_f: Expression,
                 then_f: Expression,
                 else_f: Expression
                 ):
        self.if_f = if_f
        self.then_f = then_f
        self.else_f = else_f

        self.sub_exprs = [self.if_f, self.then_f, self.else_f]
        super().__init__()

    @classmethod
    def make(cls,
             if_f: Expression,
             then_f: Expression,
             else_f: Expression
             ) -> 'AIfExpr':
        out = (cls)(None, if_f=if_f, then_f=then_f, else_f=else_f)
        return out.annotate1().simplify1()

    def __str__(self):
        return (f"if {self.sub_exprs[AIfExpr.IF  ].str}"
                f" then {self.sub_exprs[AIfExpr.THEN].str}"
                f" else {self.sub_exprs[AIfExpr.ELSE].str}")

def IF(IF: Expression,
       THEN: Expression,
       ELSE: Expression,
       annotations=None
       ) -> AIfExpr:
    return AIfExpr.make(IF, THEN, ELSE)


class Quantee(Expression):
    """represents the description of quantification, e.g., `x in T` or `(x,y) in P`
    The `Concept` type may be qualified, e.g. `Concept[Color->Bool]`

    Attributes:
        vars (List[List[Variable]]): the (tuples of) variables being quantified

        subtype (Type, Optional): a literal Type to quantify over, e.g., `Color` or `Concept[Color->Bool]`.

        sort (SymbolExpr, Optional): a dereferencing expression, e.g.,. `$(i)`.

        sub_exprs (List[SymbolExpr], Optional): the (unqualified) type or predicate to quantify over,
        e.g., `[Color], [Concept] or [$(i)]`.

        arity (int): the length of the tuple of variables

        decl (SymbolDeclaration, Optional): the (unqualified) Declaration to quantify over, after resolution of `$(i)`.
        e.g., the declaration of `Color`
    """
    def __init__(self, parent,
                 vars: Union[List[Variable], List[List[Variable]]],
                 subtype: Optional[Type] = None,
                 sort: Optional[SymbolExpr] = None):
        self.subtype = subtype
        sort = sort
        if self.subtype:
            self.check(self.subtype.name == CONCEPT or self.subtype.out is None,
                   f"Can't use signature after predicate {self.subtype.name}")

        self.sub_exprs = ([sort] if sort else
                          [self.subtype] if self.subtype else
                          [])
        self.arity = None
        self.vars : List[List[Variable]] = []
        for i, v in enumerate(vars):
            if hasattr(v, 'vars'):  # varTuple
                self.check(1 < len(v.vars), f"Can't have singleton in binary quantification")
                self.vars.append(v.vars)
                self.arity = len(v.vars) if self.arity == None else self.arity
            else:
                assert isinstance(v, Variable), "Internal error"
                self.vars.append([v])
                self.arity = 1 if self.arity == None else self.arity

        super().__init__()
        self.decl = None

        self.check(all(len(v) == self.arity for v in self.vars),
                    f"Inconsistent tuples in {self}")

    @classmethod
    def make(cls,
             var: List[Variable],
             subtype: Optional[Type] = None,
             sort: Optional[SymbolExpr] = None
             ) -> 'Quantee':
        out = (cls) (None, [var], subtype=subtype, sort=sort)
        return out.annotate1()

    def __str__(self):
        signature = ("" if len(self.sub_exprs) <= 1 else
                     f"[{','.join(t.str for t in self.sub_exprs[1:-1])}->{self.sub_exprs[-1]}]"
        )
        return (f"{','.join(str(v) for vs in self.vars for v in vs)}"
                f"{f' ∈ {self.sub_exprs[0]}' if self.sub_exprs else ''}"
                f"{signature}")


def split_quantees(self):
    """replaces an untyped quantee `x,y,z` into 3 quantees,
    so that each variable can have its own sort

    Args:
        self: either a AQuantification, AAggregate or Rule"""
    if len(self.quantees)==1 and not self.quantees[0].sub_exprs:
        # separate untyped variables, so that they can be typed separately
        q = self.quantees.pop()
        for vars in q.vars:
            for var in vars:
                self.quantees.append(Quantee.make(var, sort=None))


class AQuantification(Expression):
    """ASTNode representing a quantified formula

    Args:
        annotations (dict[str, str]):
            The set of annotations given by the expert in the IDP-Z3 program.

            ``annotations['reading']`` is the annotation
            giving the intended meaning of the expression (in English).

        q (str): either '∀' or '∃'

        quantees (List[Quantee]): list of variable declarations

        f (Expression): the formula being quantified

        supersets, new_quantees, vars1: attributes used in `interpret`
    """
    PRECEDENCE = 20

    def __init__(self, parent, annotations, q, quantees, f):
        self.annotations = annotations
        self.q = q
        self.quantees: List[Quantee] = quantees
        self.f = f

        self.q = ('∀' if self.q in ['!', 'forall'] else
                  '∃' if self.q in ["?", "thereisa"] else
                  self.q)
        split_quantees(self)

        self.sub_exprs = [self.f]
        super().__init__()

        self.type = BOOL
        self.supersets: List[List[List[Union[Identifier, Variable]]]] = None
        self.new_quantees: List[Quantee] = None
        self.vars1 : List[Variable] = None

    @classmethod
    def make(cls,
             q: str,
             quantees: List[Quantee],
             f: Expression,
             annotations=None
             ) -> 'AQuantification':
        "make and annotate a quantified formula"
        out = cls(None, annotations, q, quantees, f)
        return out.annotate1()

    def __str__(self):
        if len(self.sub_exprs) == 0:
            body = TRUE.str if self.q == '∀' else FALSE.str
        elif len(self.sub_exprs) == 1:
            body = self.sub_exprs[0].str
        else:
            connective = '∧' if self.q == '∀' else '∨'
            body = connective.join("("+e.str+")" for e in self.sub_exprs)

        if self.quantees:
            vars = ','.join([f"{q}" for q in self.quantees])
            return f"{self.q} {vars}: {body}"
        else:
            return body

    def __deecopy__(self, memo):
        # also called by AAgregate
        out = Expression.__deecopy__(self, memo)
        out.quantees = [deepcopy(q, memo) for q in out.quantees]
        return out

    def collect(self, questions, all_=True, co_constraints=True):
        questions.append(self)
        if all_:
            Expression.collect(self, questions, all_, co_constraints)
            for q in self.quantees:
                q.collect(questions, all_, co_constraints)

    def collect_symbols(self, symbols=None, co_constraints=True):
        symbols = Expression.collect_symbols(self, symbols, co_constraints)
        for q in self.quantees:
            q.collect_symbols(symbols, co_constraints)
        return symbols

def FORALL(qs, expr, annotations=None):
    return AQuantification.make('∀', qs, expr, annotations)
def EXISTS(qs, expr, annotations=None):
    return AQuantification.make('∃', qs, expr, annotations)


class Operator(Expression):
    PRECEDENCE = 0  # monkey-patched
    MAP: dict[str, Callable] = dict()  # monkey-patched
    NORMAL = {
        "is strictly less than": "<",
        "is less than": "≤",
        "=<": "≤",
        "is greater than": "≥",
        "is strictly greater than": ">",
        ">=" : "≥",
        "is not": "≠",
        "~=": "≠",
        "<=>": "⇔",
        "is the same as": "⇔",
        "are necessary and sufficient conditions for": "⇔",
        "<=": "⇐",
        "are necessary conditions for": "⇐",
        "=>": "⇒",
        "then": "⇒",
        "are sufficient conditions for": "⇒",
        "|": "∨",
        "or": "∨",
        "&": "∧",
        "and": "∧",
        "*": "⨯",
        "is": "=",
    }

    def __init__(self, parent, operator, sub_exprs, annotations=None):
        self.operator = operator
        self.sub_exprs = sub_exprs

        self.operator = list(map(
            lambda op: Operator.NORMAL.get(op, op)
            , self.operator))

        super().__init__(parent)

        self.type = BOOL if self.operator[0] in '&|∧∨⇒⇐⇔' \
               else BOOL if self.operator[0] in '=<>≤≥≠' \
               else None

    @classmethod
    def make(cls,
             ops: Union[str, List[str]],
             operands: List[Expression],
             annotations=None,
             parent=None
             ) -> Expression:
        """ creates a BinaryOp
            beware: cls must be specific for ops !
        """
        if len(operands) == 0:
            if cls == AConjunction:
                out = copy(TRUE)
            elif cls == ADisjunction:
                out = copy(FALSE)
            else:
                assert False, "Internal error"
        elif len(operands) == 1:
            return operands[0]
        else:
            if isinstance(ops, str):
                ops = [ops] * (len(operands)-1)
            out = (cls)(parent, ops, operands, annotations)

        if parent:  # for error messages
            out._tx_position = parent. _tx_position
            out._tx_position_end = parent. _tx_position_end
        if annotations:
            out.annotations = annotations
        return out.annotate1().simplify1()

    def __str__(self):
        def parenthesis(precedence, x):
            return f"({x.str})" if type(x).PRECEDENCE <= precedence else f"{x.str}"
        precedence = type(self).PRECEDENCE
        temp = parenthesis(precedence, self.sub_exprs[0])
        for i in range(1, len(self.sub_exprs)):
            temp += f" {self.operator[i-1]} {parenthesis(precedence, self.sub_exprs[i])}"
        return temp

    def collect(self, questions, all_=True, co_constraints=True):
        if self.operator[0] in '=<>≤≥≠':
            questions.append(self)
        for e in self.sub_exprs:
            e.collect(questions, all_, co_constraints)

class AImplication(Operator):
    PRECEDENCE = 50

def IMPLIES(exprs, annotations=None):
    return AImplication.make('⇒', exprs, annotations)


class AEquivalence(Operator):
    PRECEDENCE = 40

    # NOTE: also used to split rules into positive implication and negative implication. Please don't change.
    def split(self):
        posimpl = IMPLIES([self.sub_exprs[0], self.sub_exprs[1]])
        negimpl = RIMPLIES(deepcopy([self.sub_exprs[0], self.sub_exprs[1]]))
        return AND([posimpl, negimpl])

    def split_equivalences(self):
        out = self.update_exprs(e.split_equivalences() for e in self.sub_exprs)
        return out.split()

def EQUIV(exprs, annotations=None):
    return AEquivalence.make('⇔', exprs, annotations)


class ARImplication(Operator):
    PRECEDENCE = 30


def RIMPLIES(exprs, annotations):
    return ARImplication.make('⇐', exprs, annotations)


class ADisjunction(Operator):
    PRECEDENCE = 60

    def __str__(self):
        if not hasattr(self, 'enumerated'):
            return super().__str__()
        return f"{self.sub_exprs[0].sub_exprs[0].code} in {{{self.enumerated}}}"

def OR(exprs):
    return ADisjunction.make('∨', exprs)


class AConjunction(Operator):
    PRECEDENCE = 70

def AND(exprs):
    return AConjunction.make('∧', exprs)


class AComparison(Operator):
    PRECEDENCE = 80

    def is_assignment(self):
        # f(x)=y
        return (len(self.sub_exprs) == 2 and
                self.operator in [['='], ['≠']]
                and isinstance(self.sub_exprs[0], AppliedSymbol)
                and not self.sub_exprs[0].is_reified()
                and self.sub_exprs[1].is_value())

def EQUALS(exprs):
    return AComparison.make('=',exprs)


class ASumMinus(Operator):
    PRECEDENCE = 90


class AMultDiv(Operator):
    PRECEDENCE = 100


class APower(Operator):
    PRECEDENCE = 110


class AUnary(Expression):
    PRECEDENCE = 120
    MAP : dict[str, Callable] = dict()  # monkey-patched

    def __init__(self, parent,
                 operators: List[str],
                 f: Expression):
        self.operators = operators
        self.f = f
        self.operators = ['¬' if c in ['~', 'not'] else c for c in self.operators]
        self.operator = self.operators[0]
        self.check(all([c == self.operator for c in self.operators]),
                   "Incorrect mix of unary operators")

        self.sub_exprs = [self.f]
        super().__init__()

    @classmethod
    def make(cls, op: str, expr: Expression) -> AUnary:
        out = AUnary(None, operators=[op], f=expr)
        return out.annotate1().simplify1()

    def __str__(self):
        return f"{self.operator}({self.sub_exprs[0].str})"

def NOT(expr):
    return AUnary.make('¬', expr)


class AAggregate(Expression):
    PRECEDENCE = 130

    def __init__(self, parent,
                 aggtype: str,
                 quantees: List[Quantee],
                 lambda_: Optional[str] = None,
                 f: Optional[Expression] = None,
                 if_: Optional[Expression] = None):
        self.aggtype = aggtype
        self.quantees: List[Quantee] = quantees
        self.lambda_ = lambda_

        self.aggtype = ("#" if self.aggtype == "card" else
                        "min" if self.aggtype == "minimum" else
                        "max" if self.aggtype == "maximum" else
                        self.aggtype)
        split_quantees(self)
        self.f = TRUE if f is None and self.aggtype == "#" else f
        self.sub_exprs = [self.f]  # later: expressions to be summed
        if if_:
            self.sub_exprs.append(if_)
        self.annotated = False  # cannot test q_vars, because aggregate may not have quantee
        self.q = ''
        self.supersets, self.new_quantees, self.vars1 = None, None, None
        super().__init__()

    def __str__(self):
        # aggregates are over finite domains, and cannot have partial expansion
        if not self.annotated:
            assert len(self.sub_exprs) <= 2, "Internal error"
            vars = ",".join([f"{q}" for q in self.quantees])
            if self.aggtype in ["sum", "min", "max"]:
                out = (f"{self.aggtype}(lambda {vars} : "
                        f"{self.sub_exprs[0].str}"
                        f"{f' if {self.sub_exprs[1]}' if len(self.sub_exprs) == 2 else ''}"
                        f")" )
            else:
                out = (f"{self.aggtype}{{{vars} : "
                       f"{self.sub_exprs[0].str}"
                       f"}}")
        else:
            out = (f"{self.aggtype}{{"
                   f"{','.join(e.str for e in self.sub_exprs)}"
                   f"}}")
        return out

    def __deepcopy__(self, memo):
        return super().__deepcopy__(memo)

    def collect(self, questions, all_=True, co_constraints=True):
        if all_ or len(self.quantees) == 0:
            Expression.collect(self, questions, all_, co_constraints)
            for q in self.quantees:
                q.collect(questions, all_, co_constraints)

    def collect_symbols(self, symbols=None, co_constraints=True):
        return AQuantification.collect_symbols(self, symbols, co_constraints)


class AppliedSymbol(Expression):
    """Represents a symbol applied to arguments

    Args:
        symbol (SymbolExpr): the symbol to be applied to arguments

        is_enumerated (string): '' or 'is enumerated'

        is_enumeration (string): '' or 'in'

        in_enumeration (Enumeration): the enumeration following 'in'

        as_disjunction (Optional[Expression]):
            the translation of 'is_enumerated' and 'in_enumeration' as a disjunction

        decl (Declaration): the declaration of the symbol, if known

        in_head (Bool): True if the AppliedSymbol occurs in the head of a rule
    """
    PRECEDENCE = 200

    def __init__(self, parent,
                 symbol,
                 sub_exprs,
                 annotations=None,
                 is_enumerated='',
                 is_enumeration='',
                 in_enumeration=''):
        self.annotations = annotations
        self.symbol : Symbol = symbol
        self.sub_exprs = sub_exprs
        self.is_enumerated = is_enumerated
        self.is_enumeration = is_enumeration
        if self.is_enumeration == '∉':
            self.is_enumeration = 'not'
        self.in_enumeration = in_enumeration

        super().__init__()

        self.as_disjunction = None
        self.decl = None
        self.in_head = False

    @classmethod
    def make(cls,
             symbol: Symbol,
             args: List[Expression],
             **kwargs
             ) -> AppliedSymbol:
        out = cls(None, symbol, args, **kwargs)
        out.sub_exprs = args
        # annotate
        out.decl = symbol.decl
        return out.annotate1()

    @classmethod
    def construct(cls, constructor, args):
        out= cls.make(SYMBOL(constructor.name), args)
        out.decl = constructor
        out.variables = {}
        return out

    def __str__(self):
        out = f"{self.symbol}({', '.join([x.str for x in self.sub_exprs])})"
        if self.in_enumeration:
            enum = f"{', '.join(str(e) for e in self.in_enumeration.tuples)}"
        return (f"{out}"
                f"{ ' '+self.is_enumerated if self.is_enumerated else ''}"
                f"{ f' {self.is_enumeration} {{{enum}}}' if self.in_enumeration else ''}")

    def __deepcopy__(self, memo):
        out = super().__deepcopy__(memo)
        out.symbol = deepcopy(out.symbol)
        out.as_disjunction = deepcopy(out.as_disjunction)
        return out

    def collect(self, questions, all_=True, co_constraints=True):
        if self.decl and self.decl.name not in RESERVED_SYMBOLS:
            questions.append(self)
            if self.is_enumerated or self.in_enumeration:
                app = AppliedSymbol.make(self.symbol, self.sub_exprs)
                questions.append(app)
        self.symbol.collect(questions, all_, co_constraints)
        for e in self.sub_exprs:
            e.collect(questions, all_, co_constraints)
        if co_constraints and self.co_constraint is not None:
            self.co_constraint.collect(questions, all_, co_constraints)

    def collect_symbols(self, symbols=None, co_constraints=True):
        symbols = Expression.collect_symbols(self, symbols, co_constraints)
        self.symbol.collect_symbols(symbols, co_constraints)
        return symbols

    def has_decision(self):
        return ((self.decl.block is not None and not self.decl.block.name == 'environment')
            or any(e.has_decision() for e in self.sub_exprs))

    def type_inference(self):
        if self.symbol.decl:
            self.check(self.symbol.decl.arity == len(self.sub_exprs),
                f"Incorrect number of arguments in {self}: "
                f"should be {self.symbol.decl.arity}")
        try:
            out = {}
            for i, e in enumerate(self.sub_exprs):
                if self.decl and isinstance(e, Variable):
                    out[e.name] = self.decl.sorts[i]
                else:
                    out.update(e.type_inference())
            return out
        except AttributeError as e:
            #
            if "object has no attribute 'sorts'" in str(e):
                msg = f"Unexpected arity for symbol {self}"
            else:
                msg = f"Unknown error for symbol {self}"
            self.check(False, msg)

    def is_value(self) -> bool:
        # independent of is_enumeration and in_enumeration !
        return (type(self.decl) == Constructor
                and all(e.is_value() for e in self.sub_exprs))

    def is_reified(self):
        # independent of is_enumeration and in_enumeration !
        return (not all (e.is_value() for e in self.sub_exprs))

    def generate_constructors(self, constructors: dict):
        symbol = self.symbol.sub_exprs[0]
        if hasattr(symbol, 'name') and symbol.name in ['unit', 'heading']:
            assert type(self.sub_exprs[0]) == UnappliedSymbol, "Internal error"
            constructor = CONSTRUCTOR(self.sub_exprs[0].name)
            constructors[symbol.name].append(constructor)


class SymbolExpr(Expression):
    def __init__(self, parent, s, eval=''):
        self.eval = eval
        self.sub_exprs = [s]
        self.decl = self.sub_exprs[0].decl if not self.eval else None
        super().__init__()

    def __str__(self):
        return (f"$({self.sub_exprs[0]})" if self.eval else
                f"{self.sub_exprs[0]}")

    def is_intentional(self):
        return self.eval

class UnappliedSymbol(Expression):
    """The result of parsing a symbol not applied to arguments.
    Can be a constructor or a quantified variable.

    Variables are converted to Variable() by annotate().
    """
    PRECEDENCE = 200

    def __init__(self, parent, s):
        self.s = s
        self.name = self.s.name

        Expression.__init__(self)

        self.sub_exprs = []
        self.decl = None
        self.is_enumerated = None
        self.is_enumeration = None
        self.in_enumeration = None

    @classmethod
    def construct(cls, constructor: Constructor):
        """Create an UnappliedSymbol from a constructor
        """
        out = (cls)(None, s=SYMBOL(constructor.name))
        out.decl = constructor
        out.variables = set()
        return out

    def is_value(self): return True

    def is_reified(self): return False

    def __str__(self): return self.name

TRUEC = CONSTRUCTOR('true')
FALSEC = CONSTRUCTOR('false')

TRUE = UnappliedSymbol.construct(TRUEC)
FALSE = UnappliedSymbol.construct(FALSEC)


class Variable(Expression):
    """AST node for a variable in a quantification or aggregate

    Args:
        name (str): name of the variable

        sort (Optional[Union[Type, Symbol]]): sort of the variable, if known
    """
    PRECEDENCE = 200

    def __init__(self, parent,
                 name:str,
                 sort: Optional[Union[Type, Symbol]]=None):
        self.name = name
        sort = sort
        self.sort = sort
        assert sort is None or isinstance(sort, Type) or isinstance(sort, Symbol), \
            f"Internal error: {self}"

        super().__init__()

        self.type = sort.decl.name if sort and sort.decl else ''
        self.sub_exprs = []
        self.variables = set([self.name])

    def __str__(self): return self.name

    def __deepcopy__(self, memo):
        return self

    def annotate1(self): return self

    def has_variables(self) -> bool: return True

def VARIABLE(name: str, sort: Union[Type, Symbol]):
    return Variable(None, name, sort)


class Number(Expression):
    PRECEDENCE = 200

    def __init__(self, **kwargs):
        self.number = kwargs.pop('number')

        super().__init__()

        self.sub_exprs = []
        self.variables = set()
        self.py_value = 0 # to get the type

        ops = self.number.split("/")
        if len(ops) == 2:  # possible with str_to_IDP on Z3 value
            self.py_value = Fraction(self.number)
            self.type = REAL
        elif '.' in self.number:
            self.py_value = Fraction(self.number if not self.number.endswith('?') else
                                     self.number[:-1])
            self.type = REAL
        else:
            self.py_value = int(self.number)
            self.type = INT

    def __str__(self): return self.number

    def real(self):
        """converts the INT number to REAL"""
        self.check(self.type in [INT, REAL], f"Can't convert {self} to {REAL}")
        return Number(number=str(float(self.py_value)))

    def is_value(self): return True

    def is_reified(self): return False

ZERO = Number(number='0')
ONE = Number(number='1')


class Date(Expression):
    PRECEDENCE = 200

    def __init__(self, **kwargs):
        self.iso = kwargs.pop('iso')

        dt = (date.today() if self.iso == '#TODAY' else
                     date.fromisoformat(self.iso[1:]))
        if 'y' in kwargs:
            y = int(kwargs.pop('y'))
            m = int(kwargs.pop('m'))
            d = int(kwargs.pop('d'))
            dt = dt + relativedelta(years=y, months=m, days=d)
        self.date = dt

        super().__init__()

        self.sub_exprs = []
        self.variables = set()

        self.py_value = int(self.date.toordinal())
        self.type = DATE

    @classmethod
    def make(cls, value: int) -> Date:
        return cls(iso=f"#{date.fromordinal(value).isoformat()}")

    def __str__(self): return f"#{self.date.isoformat()}"

    def is_value(self): return True

    def is_reified(self): return False


class Brackets(Expression):
    PRECEDENCE = 200

    def __init__(self, **kwargs):
        self.f = kwargs.pop('f')
        self.annotations = kwargs.pop('annotations')
        if not self.annotations:
            self.annotations = {'reading': self.f.annotations['reading']}
        self.sub_exprs = [self.f]

        super().__init__()


    # don't @use_value, to have parenthesis
    def __str__(self): return f"({self.sub_exprs[0].str})"


class RecDef(Expression):
    """represents a recursive definition
    """
    def __init__(self, parent, name, vars, expr):
        self.parent = parent
        self.name = name
        self.vars = vars
        self.sub_exprs = [expr]

        Expression.__init__(self)

        if parent:  # for error messages
            self._tx_position = parent. _tx_position
            self._tx_position_end = parent. _tx_position_end

    def __str__(self):
        return (f"{self.name}("
                f"{', '.join(str(v) for v in self.vars)}"
                f") = {self.sub_exprs[0]}.")

Identifier = Union[AppliedSymbol, UnappliedSymbol, Number, Date]
Extension = Tuple[Optional[List[List[Identifier]]],  # None if the extension is infinite (e.g., Int)
                  Optional[Callable]]  # None if filtering is not required
