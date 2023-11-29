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
    Various utilities (in particular, OrderedSet)
"""
from __future__ import annotations
from typing import TYPE_CHECKING, Iterator, Union, Optional

from collections.abc import Iterable
from datetime import datetime
from json import JSONEncoder
import time
import tempfile
from enum import Enum, auto

if TYPE_CHECKING:
    from .Expression import Expression
    from .Parse import TupleIDP

"""
    Global Parameters:
"""

CO_CONSTR_RECURSION_DEPTH = 3
MAX_QUANTIFIER_EXPANSION = 20
RUN_FILE = tempfile.gettempdir() + "/IDP_Z3_run_log.txt"  # must be in /tmp folder for GAE

class Semantics(Enum):
    """Semantics for inductive definitions"""
    COMPLETION = auto()
    KRIPKEKLEENE = auto()
    WELLFOUNDED = auto()
    COINDUCTION = auto()
    STABLE = auto()
    RECDATA = auto()

"""
    String constants
"""

NEWL = "\n"
indented = "\n  "

BOOL = "𝔹"
INT = "ℤ"
REAL = "ℝ"
DATE = "Date"
CONCEPT = "Concept"

GOAL_SYMBOL = "goal_symbol"
RELEVANT = " relevant"  # internal.  Leading space to avoid conflict with user vocabulary
EXPAND = "expand"
ABS = "abs"
RESERVED_SYMBOLS = [BOOL, INT, REAL, DATE, CONCEPT,
                    GOAL_SYMBOL, RELEVANT, ABS, ]

DEFAULT = "default"

NOT_SATISFIABLE ="Not satisfiable."

PROCESS_TIMINGS = {'ground': 0, 'parse': 0, 'solve': 0}

""" Module that monkey-patches json module when it's imported so
JSONEncoder.default() automatically checks for a special "to_json()"
method and uses it to encode the object if found.
"""

def _default(self, obj):
    return getattr(obj.__class__, "to_json", _default.default)(obj)

_default.default = JSONEncoder.default  # Save unmodified default.
JSONEncoder.default = _default  # Replace it.


start = time.process_time()


def log(action):
    global start
    print("*** ", action, datetime.now().strftime("%H:%M:%S"), round(time.process_time()-start, 3))
    start = time.process_time()


class IDPZ3Error(Exception):
    """ raised whenever an error occurs in the conversion from AST to Z3 """
    pass


def unquote(s: str) -> str:
    if s[0] == "'" and s[-1] == "'":
        return s[1:-1]
    return s


# OrderedSet  #############################################


class OrderedSet(dict):
    """
    a list of expressions without duplicates (first-in is selected)
    """
    def __init__(self, els=[]):
        assert isinstance(els, Iterable), "Internal error in OrderedSet"
        super(OrderedSet, self).__init__(((el.code, el) for el in els))

    def append(self, el: Union[Expression, TupleIDP]):
        if el not in self:
            self[el.code] = el

    def __iter__(self) -> Iterator[Union[Expression, TupleIDP]]:
        return iter(self.values())  # instead of keys()

    def __contains__(self,
                     expression: Union[Expression, TupleIDP]
                     ) -> bool:
        return super(OrderedSet, self).__contains__(expression.code)

    def extend(self,
               more: Iterator[Union[Expression, TupleIDP]]):
        for el in more:
            self.append(el)

    # def items(self):
    #     return super(OrderedSet, self).items()

    def pop(self, key: str, default: Optional[Union[Expression, TupleIDP]] = None) -> Union[Expression, TupleIDP]:
        return super(OrderedSet, self).pop(key, default)

    def __or__(self, other: OrderedSet) -> OrderedSet:
        """returns the union of self and other.  Use: `self | other`.

        Returns:
            OrderedSet: the union of self and other
        """
        out = OrderedSet(self) # makes a copy
        out.extend(other)
        return out

    def __and__(self, other: OrderedSet) -> OrderedSet:
        """returns the intersection of self and other.  Use: `self & other`.

        Returns:
            OrderedSet: the intersection of self and other
        """
        out = OrderedSet({v for v in self if v in other})
        return out

    def __xor__(self, other: OrderedSet) -> OrderedSet:
        """returns the self minus other.  Use: `self ^ other`.

        Returns:
            OrderedSet: self minus other
        """
        out = OrderedSet({v for v in self if v not in other})
        return out


# redirection #############################################
# https://stackoverflow.com/a/22434728/474491

import os
import sys
from contextlib import contextmanager

def fileno(file_or_fd):
    fd = getattr(file_or_fd, 'fileno', lambda: file_or_fd)()
    if not isinstance(fd, int):
        raise ValueError("Expected a file (`.fileno()`) or a file descriptor")
    return fd

@contextmanager
def redirect_stdout(to=os.devnull, stdout=None):
    if stdout is None:
       stdout = sys.stdout

    stdout_fd = fileno(stdout)
    # copy stdout_fd before it is overwritten
    #NOTE: `copied` is inheritable on Windows when duplicating a standard stream
    with os.fdopen(os.dup(stdout_fd), 'wb') as copied:
        stdout.flush()  # flush library buffers that dup2 knows nothing about
        try:
            os.dup2(fileno(to), stdout_fd)  # $ exec >&to
        except ValueError:  # filename
            with open(to, 'wb') as to_file:
                os.dup2(to_file.fileno(), stdout_fd)  # $ exec > to
        try:
            yield stdout # allow code to be run with the redirected stdout
        finally:
            # restore stdout to its previous value
            #NOTE: dup2 makes stdout_fd inheritable unconditionally
            stdout.flush()
            os.dup2(copied.fileno(), stdout_fd)  # $ exec >&copied

def redirect_stderr_to_stdout():  # $ exec 2>&1
    return redirect_stdout(to=sys.stdout, stdout=sys.stderr)
