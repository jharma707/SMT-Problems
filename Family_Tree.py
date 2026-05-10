"""Option 3 — Family-tree puzzle (EUF + LIA).

Given a finite collection of named people, some age facts, and some
parent facts, decide whether the puzzle is consistent and, if so,
return one valid age assignment for everyone.

Every puzzle is governed by the *generation gap rule*: a parent must
be at least `GENERATION_GAP` years older than their child. This rule
applies automatically to every parent-child pair the puzzle declares
(both explicitly via "parent_of" facts and implicitly via the
"same_parent" facts, whose shared parent must still be one of the
named people).

### Input / Output

    solve_family_tree(people, age_facts, parent_facts) -> dict[str, int] | None

    people        : list of distinct name strings, e.g. ["Alice", "Bob"].
    age_facts     : list of `AgeFact` records (see `family_tree.py`).
    parent_facts  : list of `ParentFact` records (see `family_tree.py`).

    Return a dict mapping every name in `people` to a non-negative
    integer age that satisfies every fact and the generation gap rule.
    Return None if no such assignment exists.

### Z3 primitives you may use

You may only use the Z3 primitives imported below. Do not use anything
else from Z3.

    DeclareSort(name)        a fresh uninterpreted sort (i.e. type)
    Const(name, sort)        a constant of the given sort
    Function(name, *sorts)   an uninterpreted function from the first
                             sorts to the last. Returns a callable
                             that you can apply with `()` like a
                             normal Python function.
    IntSort()                the integer sort
    Distinct(*xs)            all of the given expressions are pairwise distinct
    Or(a, b, ...)            disjunction
    And(a, b, ...)           conjunction
    Not(a)                   negation
    Implies(a, b)            logical implication
    If(c, a, b)              SMT-level if-then-else expression
    Solver()                 supports s.add(...), s.check(), s.model()
    sat, unsat               result possibilities

Z3 expressions support `+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>`, `>=`
natively as Python operators. For an integer expression `e`,
`m.evaluate(e).as_long()` returns its Python int value in model `m`.
"""
from z3 import (
    DeclareSort, Const, Function, IntSort, Distinct,
    Or, And, Not, Implies, If, Solver, sat, unsat,
)
from typing import NamedTuple, Union

GENERATION_GAP = 16

class AgeFact(NamedTuple):
    person: str
    op: str
    value: Union[int, str]

class ParentFact(NamedTuple):
    kind: str           # "parent_of" or "same_parent"
    a: str              # for parent_of: the child; for same_parent: first sibling
    b: str              # for parent_of: the parent; for same_parent: second sibling



def solve_family_tree(people, age_facts, parent_facts):
    s = Solver()
    P = DeclareSort('Person')
    f = Function('f', P, IntSort())
    g = Function('g', P, P)

    person_to_const = { person: Const(person, P) for person in people }

    def encode_fact(fact, bin_op):
        s.add(f(person_to_const[fact.person]) >= 0)

        if isinstance(fact.value, int):
            s.add(bin_op(f(person_to_const[fact.person]), fact.value))
        elif isinstance(fact.value, str):
            s.add(bin_op(f(person_to_const[fact.person]), f(person_to_const[fact.value])))

    for fact in age_facts:
        if fact.op == '==':
            encode_fact(fact, lambda x, y: x == y)
        elif fact.op == '!=':
            encode_fact(fact, lambda x, y: x != y)
        elif fact.op == '<':
            encode_fact(fact, lambda x, y: x < y)
        elif fact.op == '<=':
            encode_fact(fact, lambda x, y: x <= y)
        elif fact.op == '>':
            encode_fact(fact, lambda x, y: x > y)
        elif fact.op == '>=':
            encode_fact(fact, lambda x, y: x >= y)

    for fact in parent_facts:
        if fact.kind == 'parent_of':
            s.add(g(person_to_const[fact.a]) == person_to_const[fact.b])
            s.add(f(person_to_const[fact.b]) - f(person_to_const[fact.a]) >= GENERATION_GAP)
        elif fact.kind == 'same_parent':
            s.add(g(person_to_const[fact.a]) == g(person_to_const[fact.b]))

            possible_parents = []
            for name, parent in person_to_const.items():
                possible_parents.append(
                    If(g(person_to_const[fact.a]) == parent,
                       And(f(parent) - f(person_to_const[fact.a]) >= GENERATION_GAP,
                           f(parent) - f(person_to_const[fact.b]) >= GENERATION_GAP),
                       False)
                )
            s.add(Or(possible_parents))

    if s.check() == sat:
        m = s.model()
        return { name: m.evaluate(f(person)).as_long() for name, person in person_to_const.items() }
    else:
        return None
