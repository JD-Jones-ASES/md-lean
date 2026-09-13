#!/usr/bin/env python3
# -*- coding: ascii -*-
"""
MAZUR DART WEIGHTS AND DIRICHLET ROW SUMS.

THEOREMS
--------
  (L-PN) For heights in {0,...,T} on n vertices, the one-sided
      neighbour sums P(s) and N(s) are at most (n-1) T.

  (L-W) Interior dart weights are P or N, hence <= (n-1) T.
      Boundary darts used by the matrix are not these weights:
      boundary rows of M are unit rows.

  (L-ROW) An interior Dirichlet row has ell_1-norm
      2 * sum_t w(s,t) <= 2 (n-1)^2 T.
      A boundary row has ell_1-norm 1.

  (T-DET) Therefore |det M| <= (2 (n-1)^2 T)^n when n >= 2
      and T >= 1 (so 1 <= 2 (n-1)^2 T).

  (T-DENOM) If also T <= 2^{n-2}, then
      T^2 |det M| <= 2^{n^2+n-4} (n-1)^{2n}.

EXTERNAL INPUTS
---------------
  Mazur 2026-09-09 Sec. 3 for the weight recipe and the shape
  of M.  Proofs and the (n-1) tightening are in-house.
  Span census for T <= 2^{n-2}; bits census for the n^2 (looser) arithmetic.

HONESTY
-------
 (1) Graphs are simple (symmetric, irreflexive).  Heights are
     injective in the census; the P/N bound does not need that.
 (2) Two P/N engines (graph vs Adj-free).  Two det engines on
     every n=3 matrix (permutation vs cofactor).  Two power
     engines on the arithmetic identity.
 (3) Not SPRC.  Not polynomial area.  Invertibility of M is
     Mazur's maximum principle, not claimed here.
"""
from __future__ import print_function

import itertools
import sys
import time

T0 = time.time()
FAILS = []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    line = "[%s] %s" % (tag, name)
    if detail:
        line += "  (%s)" % detail
    print(line)
    sys.stdout.flush()
    if not ok:
        FAILS.append(name)


def note(text):
    print("       " + text)
    sys.stdout.flush()


def head(text):
    print()
    print(text)
    print("-" * min(len(text), 72))
    sys.stdout.flush()


def ipow(a, e):
    x = 1
    i = 0
    while i < e:
        x *= a
        i += 1
    return x


def abs_z(x):
    if x < 0:
        return -x
    return x


def posdiff(a, b):
    if a > b:
        return a - b
    return 0


def P_loop(Adj, h, s, n):
    tot = 0
    t = 0
    while t < n:
        if Adj[s][t]:
            tot += posdiff(h[t], h[s])
        t += 1
    return tot


def N_loop(Adj, h, s, n):
    tot = 0
    t = 0
    while t < n:
        if Adj[s][t]:
            tot += posdiff(h[s], h[t])
        t += 1
    return tot


def P_all(h, s, n):
    """Second engine: ignore Adj, sum positive diffs to every other vertex."""
    tot = 0
    t = 0
    while t < n:
        if t != s:
            tot += posdiff(h[t], h[s])
        t += 1
    return tot


def N_all(h, s, n):
    tot = 0
    t = 0
    while t < n:
        if t != s:
            tot += posdiff(h[s], h[t])
        t += 1
    return tot


def ipow2(a, e):
    """Second power engine: binary exponentiation."""
    x = 1
    b = a
    k = e
    while k > 0:
        if k & 1:
            x *= b
        b *= b
        k >>= 1
    return x


def det_3x3(A):
    a, b, c = A[0]
    d, e, f = A[1]
    g, h, i = A[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def dart_w(Adj, h, B, P, N, s, t, n):
    if s == t or not Adj[s][t]:
        return 0
    if s in B:
        return 1
    if h[t] > h[s]:
        return N[s]
    if h[t] < h[s]:
        return P[s]
    return 0


def matrix_M(Adj, h, B, n):
    P = [P_loop(Adj, h, s, n) for s in range(n)]
    N = [N_loop(Adj, h, s, n) for s in range(n)]
    M = [[0 for _ in range(n)] for _ in range(n)]
    s = 0
    while s < n:
        if s in B:
            M[s][s] = 1
        else:
            t = 0
            wsum = 0
            while t < n:
                w = dart_w(Adj, h, B, P, N, s, t, n)
                wsum += w
                if s != t:
                    M[s][t] = -w
                t += 1
            M[s][s] = wsum
        s += 1
    return M, P, N


def row_l1(M, s, n):
    tot = 0
    t = 0
    while t < n:
        tot += abs_z(M[s][t])
        t += 1
    return tot


def det_perm(A):
    n = len(A)
    total = 0
    for p in itertools.permutations(range(n)):
        sign = 1
        i = 0
        while i < n:
            j = i + 1
            while j < n:
                if p[i] > p[j]:
                    sign = -sign
                j += 1
            i += 1
        prod = sign
        i = 0
        while i < n:
            prod *= A[i][p[i]]
            i += 1
        total += prod
    return total


def undirected_graphs(n):
    """Symmetric irreflexive 0-1 Adj matrices."""
    pairs = []
    i = 0
    while i < n:
        j = i + 1
        while j < n:
            pairs.append((i, j))
            j += 1
        i += 1
    e = len(pairs)
    out = []
    bits = 0
    while bits < (1 << e):
        Adj = [[False] * n for _ in range(n)]
        k = 0
        while k < e:
            if bits & (1 << k):
                i, j = pairs[k]
                Adj[i][j] = True
                Adj[j][i] = True
            k += 1
        out.append(Adj)
        bits += 1
    return out


def injective_heights(n, T):
    """Injections Fin n -> {0,...,T}."""
    return list(itertools.permutations(range(T + 1), n))


def subsets(n):
    out = []
    bits = 0
    while bits < (1 << n):
        B = set()
        i = 0
        while i < n:
            if bits & (1 << i):
                B.add(i)
            i += 1
        out.append(B)
        bits += 1
    return out


def main():
    head("Mazur weights and Dirichlet rows")
    note("stdlib only; two P/N engines; two det engines; two powers")
    note("tighter (n-1) bound; not SPRC")

    head("[A]  P/N <= (n-1) T, two engines")
    pn_ok = True
    engines_ok = True
    for n in (2, 3, 4):
        T = n + 1
        for h in injective_heights(n, T):
            h = list(h)
            Tm = max(h) if h else 0
            s = 0
            while s < n:
                Pall = P_all(h, s, n)
                Nall = N_all(h, s, n)
                if Pall > (n - 1) * Tm or Nall > (n - 1) * Tm:
                    pn_ok = False
                s += 1
            for Adj in undirected_graphs(n):
                s = 0
                while s < n:
                    Pl = P_loop(Adj, h, s, n)
                    Nl = N_loop(Adj, h, s, n)
                    Pall = P_all(h, s, n)
                    Nall = N_all(h, s, n)
                    if Pl > Pall or Nl > Nall:
                        engines_ok = False
                    if Pl > (n - 1) * Tm or Nl > (n - 1) * Tm:
                        pn_ok = False
                    s += 1
    check("P,N on a graph <= ignoring Adj", engines_ok)
    check("P,N <= (n-1) T on injective heights, n=2,3,4", pn_ok)

    head("[B]  Dirichlet rows, n=3, T=max height")
    n = 3
    n_mat = 0
    row_ok = True
    det_ok = True
    denom_ok = True
    w_ok = True
    engines_det = True
    for Adj in undirected_graphs(n):
        for h in injective_heights(n, n - 1):
            h = list(h)
            T = max(h)
            if T < 1:
                continue
            for B in subsets(n):
                M, P, N = matrix_M(Adj, h, B, n)
                n_mat += 1
                s = 0
                while s < n:
                    t = 0
                    while t < n:
                        if s not in B and Adj[s][t] and s != t:
                            w = dart_w(Adj, h, B, P, N, s, t, n)
                            if w > (n - 1) * T:
                                w_ok = False
                        t += 1
                    r = row_l1(M, s, n)
                    cap = 2 * (n - 1) * (n - 1) * T
                    if s in B:
                        if r != 1:
                            row_ok = False
                    else:
                        wsum = 0
                        t = 0
                        while t < n:
                            wsum += dart_w(Adj, h, B, P, N, s, t, n)
                            t += 1
                        if r != 2 * wsum:
                            row_ok = False
                        if r > cap:
                            row_ok = False
                    s += 1
                d1 = det_perm(M)
                d2 = det_3x3(M)
                if d1 != d2:
                    engines_det = False
                d = abs_z(d1)
                R = ipow(2 * (n - 1) * (n - 1) * T, n)
                if d > R:
                    det_ok = False
                if T <= (1 << (n - 2)):
                    Q = T * T * d
                    right = (1 << (n * n + n - 4)) * ipow(n - 1, 2 * n)
                    if Q > right:
                        denom_ok = False
    check("interior weights <= (n-1) T", w_ok)
    check("boundary row ell_1 = 1; interior = 2 sum w <= 2(n-1)^2 T",
          row_ok, "matrices=%d" % n_mat)
    check("perm det = 3x3 cofactor on every matrix", engines_det)
    check("|det M| <= (2 (n-1)^2 T)^n", det_ok)
    check("T^2 |det| <= 2^{n^2+n-4} (n-1)^{2n} when T <= 2^{n-2}",
          denom_ok)

    head("[C]  tighter arithmetic, n=2..10, T=2^{n-2}")
    arith_ok = True
    pow_ok = True
    n = 2
    while n <= 10:
        T = 1 << (n - 2)
        m = n - 1
        left = ipow(T, 2) * ipow(2 * m * m * T, n)
        right = (1 << (n * n + n - 4)) * ipow(m, 2 * n)
        if left != right:
            arith_ok = False
        if ipow(m, 2 * n) != ipow2(m, 2 * n):
            pow_ok = False
        leftg = left * T
        rightg = (1 << (n * n + 2 * n - 6)) * ipow(m, 2 * n)
        if leftg != rightg:
            arith_ok = False
        n += 1
    check("ipow == binary exp on (n-1)^{2n}, n=2..10", pow_ok)
    check("equality at T=2^{n-2}: Q and QT with (n-1)", arith_ok)

    head("[D]  (n-1) beats n for n>=3")
    n = 3
    T = 1 << (n - 2)
    loose = (1 << (n * n + n - 4)) * ipow(n, 2 * n)
    tight = (1 << (n * n + n - 4)) * ipow(n - 1, 2 * n)
    check("(n-1)^{2n} < n^{2n} at n=3", tight < loose,
          "tight=%s loose=%s" % (tight, loose))

    print()
    print("-" * 72)
    print("checks run through; failures: %d   (%.1f s)"
          % (len(FAILS), time.time() - T0))
    print()
    print("EXTERNAL DEPENDENCIES")
    print("  Mazur Sec. 3 weight recipe (re-implemented, not cited as a number)")
    print()
    print("NOT CLAIMED: SPRC; polynomial area; that M is invertible")
    print("beyond the census (the paper's maximum principle is not here).")
    print()
    if FAILS:
        print("FAILED:")
        for n in FAILS:
            print("  -", n)
        print()
        print("CERTIFICATE RED")
        sys.exit(1)
    print("CERTIFICATE GREEN")


if __name__ == "__main__":
    main()
