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

Classes to store assignments of values to questions

"""
from __future__ import annotations

__all__ = ["Status", "Assignment", "Assignments"]


from copy import copy, deepcopy
from enum import Enum, auto
from typing import Optional, Tuple, TYPE_CHECKING
from z3 import BoolRef

from .Expression import Expression, TRUE, FALSE, NOT, EQUALS, AppliedSymbol
from .utils import NEWL, BOOL, INT, REAL, DATE

if TYPE_CHECKING:
    from .Parse import SymbolDeclaration, Enumeration
    from .Theory import Theory


class Status(Enum):
    """Describes how the value of a question was obtained"""
    UNKNOWN = auto()
    # fixed values:
    STRUCTURE = auto()
    UNIVERSAL = auto()
    CONSEQUENCE = auto()
    ENV_CONSQ = auto()
    # choices:
    EXPANDED = auto()
    DEFAULT = auto()
    GIVEN = auto()


class Assignment(object):
    """Represent the assignment of a value to a question.
    Questions can be:

    * predicates and functions applied to arguments,
    * comparisons,
    * outermost quantified expressions

    A value is a rigid term.

    An assignment also has a reference to the symbol under which it should be
    displayed.

    Attributes:
        sentence (Expression): the question to be assigned a value

        value (Expression, optional): a rigid term

        status (Status, optional): qualifies how the value was obtained

        is_certainly_undefined (bool): True for functions applied to arguments certainly outside of its domain

        relevant (bool, optional): states whether the sentence is relevant

        symbol_decl (SymbolDeclaration): declaration of the symbol under which
        it should be displayed in the IC.
    """
    def __init__(self,
                 sentence: Expression,
                 value: Optional[Expression],
                 status: Optional[Status],
                 relevant: Optional[bool] = True):
        self.sentence: Expression = sentence
        self.value: Optional[Expression] = value
        self.status: Optional[Status] = status
        self.is_certainly_undefined = False
        self.relevant: Optional[bool] = relevant

        # First symbol in the sentence, preferably not starting with '_':
        # if no public symbol (not starting with '_') is found, the first
        # private one is used.
        self.symbol_decl: Optional[SymbolDeclaration] = None
        default = None
        self.symbols: dict[str, SymbolDeclaration] = \
            sentence.collect_symbols(co_constraints=False).values()
        for d in self.symbols:
            if not d.private:
                if d.block:  # ignore accessors and testers
                    self.symbol_decl = d
                    break
            elif default is None:
                default = d
        if not self.symbol_decl:  # use the '_' symbol (to allow relevance computation)
            self.symbol_decl = default

    def copy(self,
             shallow: Optional[bool] =False
             ) -> Assignment:
        out = copy(self)
        if not shallow:
            out.sentence = deepcopy(out.sentence)
        return out

    def __str__(self) -> str:
        pre, post = '', ''
        if self.value is None:
            pre = "? "
        elif self.value.same_as(TRUE):
            pre = ""
        elif self.value.same_as(FALSE):
            pre = "Not "
        else:
            post = f" -> {str(self.value)}"
        return f"{pre}{self.sentence.annotations['reading']}{post}"

    def __repr__(self) -> str:
        return self.__str__()

    def __log__(self) -> Optional[Expression]:
        return self.value

    def same_as(self, other: Assignment) -> bool:
        """returns True if self has the same sentence and truth value as other.

        Args:
            other (Assignment): an assignment

        Returns:
            bool: True if self has the same sentence and truth value as other.
        """
        return (self.sentence.same_as(other.sentence)
                and ((self.value is None and other.value is None)
                     or (self.value is not None and other.value is not None
                         and self.value.same_as(other.value))))

    def to_json(self) -> str:  # for GUI
        return str(self)

    def formula(self) -> Expression:
        if self.value is None:
            raise Exception("can't translate unknown value")
        if self.sentence.type == BOOL:
            out = self.sentence if self.value.same_as(TRUE) else \
                NOT(self.sentence)
        else:
            out = EQUALS([self.sentence, self.value])
        return out

    def negate(self) -> Assignment:
        """returns an Assignment for the same sentence, but an opposite truth value.

        Raises:
            AssertionError: Cannot negate a non-boolean assignment

        Returns:
            [type]: returns an Assignment for the same sentence, but an opposite truth value.
        """
        assert self.sentence.type == BOOL, "Cannot negate a non-boolean assignment"
        assert self.value is not None, "Cannot negate an assignment without value"
        value = FALSE if self.value.same_as(TRUE) else TRUE
        return Assignment(self.sentence, value, self.status, self.relevant)

    def translate(self, problem: Theory) -> BoolRef:
        return self.formula().translate(problem)

    def as_set_condition(self
             ) -> Tuple[Optional[AppliedSymbol],
                        Optional[bool],
                        Optional[Enumeration]]:
        """returns an equivalent set condition, or None

        Returns:
            Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]: meaning "appSymb is (not) in enumeration"
        """
        (x, y, z) = self.sentence.as_set_condition()
        assert self.value is not None, "Internal error"
        if x:
            return (x, y if self.value.same_as(TRUE) else not y, z)
        return (None, None, None)

    def unset(self) -> None:
        """ Unsets the value of an assignment.

        Returns:
            None
        """
        self.value = None
        self.status = Status.UNKNOWN

class Assignments(dict):
    """Contains a set of Assignment"""
    def __init__(self, *arg, **kw):
        super(Assignments, self).__init__(*arg, **kw)
        self.symbols: dict[str, SymbolDeclaration] = {}
        for a in self.values():
            if a.symbol_decl:
                self.symbols[a.symbol_decl.name] = a.symbol_decl

    def copy(self, shallow: bool = False) -> "Assignments":
        return Assignments({k: v.copy(shallow) for k, v in self.items()})

    def assert__(self,
                 sentence: Expression,
                 value: Optional[Expression],
                 status: Optional[Status]
                ) -> Assignment:

        if sentence.code in self:
            out = self[sentence.code].copy(shallow=True)
            if out.status in [Status.GIVEN, Status.EXPANDED, Status.DEFAULT]\
                    and status in [Status.CONSEQUENCE, Status.ENV_CONSQ, Status.UNIVERSAL]:
                assert out.value.same_as(value), \
                        "System should not override given choices with different consequences, please report this bug."
            else:
                if not (out.status == Status.ENV_CONSQ and status == Status.CONSEQUENCE):
                    # do not change an env consequence to a decision consequence
                    out.value = value
                    out.status = status
        else:
            out = Assignment(sentence, value, status)
        if out.symbol_decl:  # ignore comparisons of constructors
            self[sentence.code] = out
            self.symbols[out.symbol_decl.name] = out.symbol_decl
        return out

    def __str__(self) -> str:
        """ Print the assignments in the same format as a model.

        Most symbols are printed as `name := {(val1, ..., val} -> valx, ...}.`
        with the exception of nullary symbols, which are printed as
        `name := value`.
        """
        out : dict[SymbolDeclaration, dict[str, str]] = {}  # ordered set of strings
        nullary = set()
        for a in self.values():
            if type(a.sentence) == AppliedSymbol:
                args = ", ".join(str(e) for e in a.sentence.sub_exprs)
                args = f"({args})" if 1 < len(a.sentence.sub_exprs) else args

                c = None
                if a.symbol_decl.arity == 0:
                    # Symbol is a proposition or constant.
                    c = f"{str(a.value)}" if a.value is not None else "*"
                    nullary.add(a.symbol_decl)
                elif a.value == FALSE:
                    # make sure we have an entry for `a` in `out`
                    if a.symbol_decl not in out:
                        out[a.symbol_decl] = {}
                elif a.value == TRUE:
                    # Symbol is a predicate.
                    c = f"{args}"
                elif a.value is not None:
                    # Symbol is a function.
                    c = f"{args} -> {str(a.value)}"

                if c:
                    enum = out.get(a.symbol_decl, dict())
                    enum[c] = c
                    out[a.symbol_decl] = enum

        model_str = ""
        for k, enum in out.items():
            if k in nullary:  # do not use {...}
                val = f"{k.name} := {list(enum)[0]}.{NEWL}"
                if "*" in val:
                    val = f"// {val}"
            else:
                sign = ':=' if k.instances or k.out.name == BOOL else '>>'
                # TODO improve sign detection (using base_type/extension, interpretation)
                # needs access to the theory !
                finite_domain = all(s.name not in [INT, REAL, DATE]
                        for s in k.sorts)
                sign = ':=' if finite_domain or k.out.name == BOOL else '>>'
                val = f"{k.name} {sign} {{{ ', '.join(s for s in enum) }}}.{NEWL}"
                val = f"{k.name} {sign} {{{ ', '.join(s for s in enum) }}}.{NEWL}"
            model_str += val
        return model_str
