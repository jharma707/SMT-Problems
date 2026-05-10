"""Option 2 — Sliding puzzle solver.

The sliding puzzle is played on an N-by-N grid containing tiles
1, 2, ..., N**2 - 1 and one empty cell, called the *blank* (encoded as
0). A move slides any tile that shares an edge with the blank into the
blank's position; equivalently, the blank swaps with one of its (up to
four) neighbors. Decide whether `goal` is reachable from `start` in
exactly K moves, and if so return the sequence of blank positions.

### Input / Output

    solve_sliding_puzzle(N, start, goal, K) -> list[int] | None

    N     : int — board side length. The board is N-by-N.
    start : list of length N**2, row-major. Each entry is a tile id in
            0..N**2-1, with 0 representing the blank. Every tile id
            appears exactly once.
    goal  : list of length N**2, row-major, in the same format as
            `start`.
    K     : int — exact number of moves to use (K >= 0).

    Return a list of length K+1 giving the blank's position (a flat
    row-major index, 0..N**2-1) at each step, starting with the blank
    in `start` and ending with the blank in `goal`. Return None if no
    sequence of exactly K moves takes `start` to `goal`.

### Z3 primitives you may use You may only use the Z3 primitives imported below. Do not use anything else from Z3.
    Array(name, dom, rng)   fresh array variable
    IntSort()               the sort of integers
    Int(name)               fresh integer variable
    Store(arr, i, v)        array `arr` updated so index i maps to v
    Select(arr, i)          read at index i
    And(a, b, ...)          conjunction
    Or(a, b, ...)           disjunction
    Not(a)                  negation
    If(c, a, b)             SMT-level if-then-else expression
    Solver()                supports s.add(...), s.check(), s.model()
    sat, unsat              result possibilities

Z3 expressions support `+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>`, `>=`
natively as Python operators. For an integer variable `v`,
`m.evaluate(v).as_long()` returns its Python int value in model `m`.

### Hint

The spec hint suggests representing each board state as a Z3 Array from
cell index to tile, and using `Store`/`Select` at a *symbolic* index
(i.e. an index that's itself a Z3 variable, not a Python integer) to
express a move.
"""
from z3 import Array, IntSort, Int, Store, Select, And, Or, Not, If, Solver, sat, unsat

def solve_sliding_puzzle(N, start, goal, K):
    s = Solver()

    grid_movements = []
    for i in range(N**2):
        row_i = i // N
        col_i = i % N
        movements = []

        if col_i != 0:
            movements.append(i - 1)
        if col_i != N - 1:
            movements.append(i + 1)
        if row_i != 0:
            movements.append(i - N)
        if row_i != N - 1:
            movements.append(i + N)

        grid_movements.append(movements)

    def encode_move(prev_array, blank_positions, step):
        last_blank = blank_positions[-1]
        next_blank = Int(f'i_{step}')

        possible_movements = []
        for idx in range(N**2):
            neighbors = grid_movements[idx]
            possible_movements.append(If(last_blank == idx, Or([next_blank == n for n in neighbors]), False))
        s.add(Or(possible_movements))

        a0 = Store(prev_array, last_blank, Select(prev_array, next_blank))
        a1 = Store(a0, next_blank, 0)

        blank_positions.append(next_blank)
        return a1, blank_positions

    a = Array('a', IntSort(), IntSort())
    for i, e in enumerate(start):
        a = Store(a, i, e)

    initial_blank = Int('blank')
    s.add(initial_blank == start.index(0))

    final_board, blank_positions = a, [initial_blank]
    for k in range(K):
        final_board, blank_positions = encode_move(final_board, blank_positions, k)

    for i, e in enumerate(goal):
        s.add(Select(final_board, i) == e)

    if s.check() == sat:
        m = s.model()
        return [ m.evaluate(p).as_long() for p in blank_positions ]
    else:
        return None
