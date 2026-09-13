#!/usr/bin/env python3
# -*- coding: ascii -*-
"""Exact span, dart-mass, and scaling-expression checks.

Standard library only. Independent finite regression checks, not Lean
proofs. No Python assert, so python -O does not remove checks.
Not SPRC; not a grid-drawing theorem; not a claim that every
3-connected plane graph attains F(n).
"""
from __future__ import annotations

import itertools as it
import json
import random
from fractions import Fraction
from math import gcd, prod
from typing import Sequence

SEED = 20260913


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def exact_span_cap(n: int) -> int:
    if n < 2:
        raise ValueError("The span cap is defined here only for n >= 2")
    return (1 << (n // 2)) - 1 if n % 2 == 0 else 3 * (1 << ((n - 3) // 2)) - 1


def repo_join(a: int, b: int) -> int:
    """The source recurrence, not the simplified expression used in the proof."""
    w = max(b - 1, 0)
    return a + 1 if w == 0 else a + 1 + max(max(a - 1, 0), w) + w


def span_checks() -> dict:
    maxima = {2: 1}
    for n in range(3, 501):
        best = n - 1  # the n-cycle
        for a in range(2, n):
            b = n - a + 1
            best = max(best, maxima[a] + maxima[b])
            if b == 2 or (a >= 3 and b >= 3):
                best = max(best, repo_join(maxima[a], maxima[b]))
        maxima[n] = best
        require(best == exact_span_cap(n), f"univariate span n={n}")

    # All achievable (vertex count, nontrivial-join count) states, with the
    # maximum in each state. The recurrence is monotone in child spans.
    states = {2: {0: 1}}
    for n in range(3, 101):
        row = {0: n - 1}
        for a in range(2, n):
            b = n - a + 1
            for ja, A in states[a].items():
                for jb, B in states[b].items():
                    j = ja + jb
                    row[j] = max(row.get(j, -1), A + B)
                    if B == 1 or (a >= 3 and b >= 3):
                        jj = j + int(B > 1)
                        row[jj] = max(row.get(jj, -1), repo_join(A, B))
        states[n] = row
        require(set(row) == set(range((n - 3) // 2 + 1)), f"join budgets n={n}")
        for j, value in row.items():
            require(value == (1 << j) * (n - 2 * j) - 1, f"bivariate n={n}, j={j}")

    # Full attainable-span sets, independent of retaining just maxima.
    attainable = {2: {1}}
    for n in range(3, 17):
        values = {n - 1}
        for a in range(2, n):
            b = n - a + 1
            for A in attainable[a]:
                for B in attainable[b]:
                    values.add(A + B)
                    if B == 1 or (a >= 3 and b >= 3):
                        values.add(repo_join(A, B))
        attainable[n] = values
        require(min(values) == n - 1, f"minimum span n={n}")
        require(max(values) == exact_span_cap(n), f"attainable span n={n}")
    return {
        "maxima_checked_through_n": 500,
        "bivariate_checked_through_n": 100,
        "bivariate_states": sum(len(row) for row in states.values()),
        "full_attainable_span_sets_through_n": 16,
        "first_values": {str(n): maxima[n] for n in range(2, 19)},
    }


def determinant(matrix: Sequence[Sequence[int]]) -> int:
    """Bareiss fraction-free elimination, including row swaps and singular cases."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Expected a square matrix")
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    sign, previous = 1, 1
    for k in range(n - 1):
        pivot_row = next((r for r in range(k, n) if a[r][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for r in range(k + 1, n):
            for c in range(k + 1, n):
                numerator = pivot * a[r][c] - a[r][k] * a[k][c]
                require(numerator % previous == 0, "Bareiss division was not exact")
                a[r][c] = numerator // previous
        for r in range(k + 1, n):
            a[r][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def weighted_dirichlet(w: Sequence[Sequence[int]], boundary: set[int]) -> list[list[int]]:
    n = len(w)
    return [[int(s == t) if s in boundary else
             (sum(w[s]) if s == t else -w[s][t])
             for t in range(n)] for s in range(n)]


def mazur_weights(adj: Sequence[Sequence[bool]], h: Sequence[int], boundary: set[int]):
    n = len(h)
    up = [[t for t in range(n) if adj[s][t] and h[t] > h[s]] for s in range(n)]
    down = [[t for t in range(n) if adj[s][t] and h[t] < h[s]] for s in range(n)]
    P = [sum(h[t] - h[s] for t in up[s]) for s in range(n)]
    N = [sum(h[s] - h[t] for t in down[s]) for s in range(n)]
    w = [[0 if s == t or not adj[s][t] else
          (1 if s in boundary else N[s] if h[t] > h[s] else P[s] if h[t] < h[s] else 0)
          for t in range(n)] for s in range(n)]
    return w, up, down, P, N


def check_mazur_case(adj, h, boundary) -> tuple[int, list[list[int]], tuple]:
    n, T = len(h), max(h, default=0)
    w, up, down, P, N = mazur_weights(adj, h, boundary)
    M = weighted_dirichlet(w, boundary)
    interior = [s for s in range(n) if s not in boundary]
    injective = len(set(h)) == n
    for s in interior:
        a, b, mass = len(up[s]), len(down[s]), sum(w[s])
        pair_sum = sum(h[t] - h[u] for t in up[s] for u in down[s])
        require(mass == pair_sum == a * N[s] + b * P[s], "pair-sum identity")
        require(mass <= a * b * T, "degree-sensitive mass bound")
        require(sum(abs(x) for x in M[s]) == 2 * mass, "row norm identity")
        if injective:
            require(2 * mass + a * b * (a + b) <= a * b * (2 * T + 2),
                    "injective mass refinement")
        require(sum(M[s][t] * h[t] for t in range(n)) == 0, "height harmonicity")
    delta = determinant(M)
    require(0 <= delta <= prod(sum(w[s]) for s in interior), "determinant diagonal bound")
    positive = all(P[s] > 0 and N[s] > 0 for s in interior)
    require((delta > 0) == positive, "exact nonsingularity criterion")
    if interior:
        lower = prod(len(down[s]) * P[s] for s in interior)
        upper = prod(len(up[s]) * N[s] for s in interior)
        require(delta >= lower + upper, "two monotone-forest lower bounds")
    c = max(n - 1, 0) ** 2 // 4
    require(delta <= (c * T) ** len(interior), "boundary-sensitive uniform determinant bound")
    return delta, M, (w, P, N, interior)


def graph_from_mask(n: int, mask: int, undirected: bool) -> list[list[bool]]:
    adj = [[False] * n for _ in range(n)]
    pairs = list(it.combinations(range(n), 2)) if undirected else list(it.permutations(range(n), 2))
    for bit, (s, t) in enumerate(pairs):
        if (mask >> bit) & 1:
            adj[s][t] = True
            if undirected:
                adj[t][s] = True
    return adj


def exhaustive_matrix_checks() -> dict:
    small_directed, order_four = 0, 0
    for n in range(4):
        for mask in range(1 << (n * (n - 1))):
            adj = graph_from_mask(n, mask, False)
            for h in it.product(range(4), repeat=n):
                for bm in range(1 << n):
                    boundary = {i for i in range(n) if (bm >> i) & 1}
                    check_mazur_case(adj, h, boundary)
                    small_directed += 1
    for mask in range(64):
        adj = graph_from_mask(4, mask, True)
        for h in it.permutations((0, 1, 2, 5)):
            for bm in range(16):
                check_mazur_case(adj, h, {i for i in range(4) if (bm >> i) & 1})
                order_four += 1
    return {"all_directed_graphs_n_at_most_3_heights_0_to_3_all_boundaries": small_directed,
            "all_simple_undirected_graphs_n_4_permuted_heights_0_1_2_5_all_boundaries": order_four}


def forest_sum(w: Sequence[Sequence[int]], boundary: set[int]) -> int:
    n = len(w)
    interior = [s for s in range(n) if s not in boundary]
    choices = [[t for t in range(n) if w[s][t] > 0] for s in interior]
    total = 0
    for image in it.product(*choices):
        mapping = dict(zip(interior, image))
        good = True
        for s in interior:
            visited = set()
            while s not in boundary:
                if s in visited:
                    good = False
                    break
                visited.add(s)
                s = mapping[s]
            if not good:
                break
        if good:
            total += prod(w[s][t] for s, t in mapping.items())
    return total


def solve_rational(matrix: Sequence[Sequence[int]], rhs: Sequence[Fraction]) -> list[Fraction]:
    n = len(matrix)
    a = [[Fraction(x) for x in row] + [Fraction(rhs[i])] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col]), None)
        if pivot is None:
            raise ValueError("Singular system")
        a[col], a[pivot] = a[pivot], a[col]
        divisor = a[col][col]
        a[col] = [v / divisor for v in a[col]]
        for r in range(n):
            if r != col:
                factor = a[r][col]
                a[r] = [x - factor * y for x, y in zip(a[r], a[col])]
    return [row[-1] for row in a]


def additional_checks() -> dict:
    rng = random.Random(SEED)
    forests = 0
    for n in range(6):
        for _ in range(50):
            w = [[0 if s == t else rng.randrange(4) for t in range(n)] for s in range(n)]
            B = {i for i in range(n) if rng.randrange(2)}
            M = weighted_dirichlet(w, B)
            delta = determinant(M)
            require(delta == forest_sum(w, B), "independent rooted-forest expansion")
            require(0 <= delta <= prod(sum(w[s]) for s in range(n) if s not in B),
                    "generic forest determinant bound")
            forests += 1
    systems, row_reductions = 0, 0
    for _ in range(500):
        n = rng.randrange(2, 9)
        h = rng.sample(range(3 * n + 1), n)
        low = min(h)
        h = [x - low for x in h]
        adj = [[s != t and bool(rng.randrange(2)) for t in range(n)] for s in range(n)]
        # Put every local height extremum on the boundary: each remaining
        # vertex has both a strict lower and a strict higher neighbour.
        B = {s for s in range(n) if
             not any(adj[s][t] and h[t] < h[s] for t in range(n)) or
             not any(adj[s][t] and h[t] > h[s] for t in range(n))}
        delta, M, (w, P, N, interior) = check_mazur_case(adj, h, B)
        T = max(h)
        rhs = [Fraction(h[s] * (T - h[s]), T * T) if s in B else Fraction(0)
               for s in range(n)]
        X = solve_rational(M, rhs)
        Q = T * T * delta
        require(Q > 0, "positive scale")
        require(all((Q * x).denominator == 1 for x in X), "common denominator")
        require(all(0 <= x <= Fraction(1, 4) for x in X), "maximum principle")
        g = {s: gcd(P[s], N[s]) for s in interior}
        require(all(value > 0 for value in g.values()), "positive row gcds")
        primitive = [[x // g[s] if s in g else x for x in row] for s, row in enumerate(M)]
        dp = determinant(primitive)
        require(delta == prod(g.values()) * dp, "primitive determinant factorization")
        require(solve_rational(primitive, rhs) == X, "primitive rows preserve solution")
        require(all((T * T * dp * x).denominator == 1 for x in X), "primitive denominator")
        systems += 1
        row_reductions += int(any(value > 1 for value in g.values()))

    sharp_rows = 0
    for a in range(1, 7):
        for b in range(1, 7):
            T = a + b + 3
            h = [b] + list(range(b)) + list(range(T - a + 1, T + 1))
            n = len(h)
            adj = [[False] * n for _ in range(n)]
            for t in range(1, n):
                adj[0][t] = True
            B = set(range(1, n))
            delta, _, _ = check_mazur_case(adj, h, B)
            require(2 * delta == a * b * (2 * T - (a + b) + 2), "injective bound sharpness")
            sharp_rows += 1

    for a in range(1001):
        require(a ** 3 <= 3 ** a, "integer product-budget inequality")
    for e in range(1, 1001):
        require((Fraction(e) + Fraction(1, 32)) ** 2 >= e * e + Fraction(1, 16),
                "31/32 margin scalar inequality")

    # A complete exact example from the source paper's K4 normalization.
    h = [0, 1, 2, 3]
    adj = [[s != t for t in range(4)] for s in range(4)]
    delta, M, _ = check_mazur_case(adj, h, {0, 1, 3})
    X = solve_rational(M, [Fraction(0), Fraction(2, 9), Fraction(0), Fraction(0)])
    require(delta == 5 and X == [0, Fraction(2, 9), Fraction(2, 45), 0], "K4 example")
    return {"generic_weighted_forest_checks": forests,
            "rational_system_and_denominator_checks": systems,
            "systems_with_nontrivial_primitive_row_reduction": row_reductions,
            "sharp_injective_row_examples": sharp_rows,
            "integer_cube_budget_checked_through": 1000,
            "rational_margin_scalar_checked_through": 1000,
            "K4": {"determinant": delta, "Q": 45,
                   "integer_coordinates": [[int(45 * x), 45 * y] for x, y in zip(X, h)]}}


def boundary_checks() -> dict:
    count = 0
    for T in range(2, 13):
        for b in range(3, min(T + 2, 7)):
            for mids in it.combinations(range(1, T), b - 2):
                heights = (0,) + mids + (T,)
                xs = [sum(min(y, t) for t in mids) for y in heights]
                C = sum(mids)
                require(0 < C and xs[-1] == C, "boundary scale")
                for i in range(b):
                    ni = (i + 1) % b
                    for j in range(b):
                        if j in (i, ni):
                            continue
                        cross = ((xs[ni] - xs[i]) * (heights[j] - heights[i]) -
                                 (heights[ni] - heights[i]) * (xs[j] - xs[i]))
                        require(cross > 0, "strict support of alternative boundary")
                C_rev = sum(T - t for t in mids)
                require(2 * min(C, C_rev) <= (b - 2) * T, "reflected linear-height boundary budget")
                count += 1
    five_point_cases = 0
    for L in range(1, 7):
        # Exclude all integer x-coordinates in a strip of width L+1.
        # Translation lets any candidate with width <= L+1 lie in this box.
        for x in it.product(range(L + 2), repeat=5):
            strict = (x[1] - x[0] > L * (x[2] - x[1]) and
                      x[2] - x[1] > x[3] - x[2] and
                      L * (x[3] - x[2]) > x[4] - x[3])
            require(not strict, "five-point integer-width lower bound")
        x = (0, L + 1, L + 2, L + 1, 0)
        require(x[1] - x[0] > L * (x[2] - x[1]) and
                x[2] - x[1] > x[3] - x[2] and
                L * (x[3] - x[2]) > x[4] - x[3],
                "five-point minimum-width witness")
        five_point_cases += 1
    return {"alternative_strictly_convex_boundary_polygons": count,
            "largest_height": 12,
            "exact_five_point_width_cases_L_1_through_6": five_point_cases}


def bit_comparisons() -> list[dict]:
    rows = []
    for n in (4, 5, 10, 20, 50, 100):
        F = exact_span_cap(n)
        old = 2 ** (n * n + 2 * n - 6) * (n - 1) ** (2 * n)
        generic = (((n - 1) ** 2) // 4) ** (n - 3) * F ** n
        planar = 3 ** (2 * n - 7) * F ** n
        rows.append({"n": n, "old_bound_bits": old.bit_length(),
                     "sharpened_generic_bound_bits": generic.bit_length(),
                     "planar_degree_budget_bound_bits": planar.bit_length()})
    return rows


def main() -> None:
    results = {
        "scope": "Exact finite checks, not Lean certification or an audit of the source existence theorem",
        "random_seed": SEED,
        "span": span_checks(),
        "exhaustive_matrices": exhaustive_matrix_checks(),
        "additional": additional_checks(),
        "alternative_boundary": boundary_checks(),
        "bit_comparisons": bit_comparisons(),
    }
    print(json.dumps(results, indent=2))
    print()
    print("CERTIFICATE GREEN")


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print("FAILED:", error)
        print("CERTIFICATE RED")
        raise SystemExit(1)
