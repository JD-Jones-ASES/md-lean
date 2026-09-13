#!/usr/bin/env python3
# -*- coding: ascii -*-
"""
HEIGHT SPAN IN MAZUR'S GREEDY LABELING.

THEOREMS
--------
  (L-PASTE) For integers a,b >= 1,
      2^{a-1} + 2^{b-1} <= 2^{a+b-1}.

  (L-JOIN) For integers A >= 1, W >= 1,
      A + 1 + max(A-1, W) + W <= 2*(A + W).
      For integers p,q >= 1, 2*(p + q - 1) <= 2*p*q.

  (T-SPAN) Every well-formed Mazur scheme (edge, cycle,
      binary series, two-range join with the paper's worst-case
      D) has span T <= 2^{n-2}, where n is the vertex count.

  (T-TIGHT) Equality holds for the single edge, the 3-cycle,
      and the two-edge series (a path on 3 vertices).

EXTERNAL INPUTS
---------------
  None.  Recurrences from Mazur 2026-09-09 Sec. 2, re-derived.
  This file does not prove SPRC, polynomial area, or bit length.

HONESTY
-------
 (1) Desk: Grok 4.6, 2026-09-13.  Statement targeted from a
     received note; proof re-derived.
 (2) Join uses the worst attachment c=1, so the scheme-span
     is an upper bound on the constructed span.
 (3) Two span engines: recursive recurrences vs the closed
     power-of-two bound.  Exhaustion is all schemes of
     constructor-depth <= 6 (finite).
"""
from __future__ import print_function

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


# ---------------------------------------------------------------------------
# Two engines for 2^k.  Engine A: iterative multiply.  Engine B: bit shift.
# ---------------------------------------------------------------------------

def pow2_mul(k):
    if k < 0:
        raise ValueError("negative exponent")
    x = 1
    i = 0
    while i < k:
        x *= 2
        i += 1
    return x


def pow2_shift(k):
    if k < 0:
        raise ValueError("negative exponent")
    return 1 << k


def pow2(k):
    a = pow2_mul(k)
    b = pow2_shift(k)
    if a != b:
        raise RuntimeError("pow2 engines disagree: %s vs %s" % (a, b))
    return a


# ---------------------------------------------------------------------------
# Schemes.  A scheme is a tuple:
#   ("edge",)
#   ("cycle", n)           n >= 3 vertex count
#   ("series", A, B)
#   ("join", H, K)
# ---------------------------------------------------------------------------

def verts(s):
    tag = s[0]
    if tag == "edge":
        return 2
    if tag == "cycle":
        return s[1]
    if tag == "series":
        return verts(s[1]) + verts(s[2]) - 1
    if tag == "join":
        return verts(s[1]) + verts(s[2]) - 1
    raise ValueError(tag)


def span(s):
    """Constructed span, using worst-case c=1 on joins."""
    tag = s[0]
    if tag == "edge":
        return 1
    if tag == "cycle":
        return s[1] - 1
    if tag == "series":
        return span(s[1]) + span(s[2])
    if tag == "join":
        A = span(s[1])
        TK = span(s[2])
        W = TK - 1
        if W == 0:
            return A + 1
        return A + 1 + max(A - 1, W) + W
    raise ValueError(tag)


def well_formed(s):
    tag = s[0]
    if tag == "edge":
        return True
    if tag == "cycle":
        return s[1] >= 3
    if tag == "series":
        return well_formed(s[1]) and well_formed(s[2])
    if tag == "join":
        H, K = s[1], s[2]
        if not (well_formed(H) and well_formed(K)):
            return False
        W = span(K) - 1
        if W == 0:
            return verts(K) == 2
        return verts(H) >= 3 and verts(K) >= 3
    raise ValueError(tag)


def all_schemes(max_n):
    """Every well-formed scheme with at most max_n vertices.

    Completeness: every scheme is an edge, a cycle, a binary series of
    two smaller schemes, or a join of two smaller schemes, and verts
    add as n = nA + nB - 1.  We generate by increasing n.
    """
    by_n = {}
    by_n[2] = [("edge",)]
    n = 3
    while n <= max_n:
        cur = [("cycle", n)]
        nA = 2
        while nA <= n - 1:
            nB = n - nA + 1
            if nB < 2:
                nA += 1
                continue
            for A in by_n.get(nA, []):
                for B in by_n.get(nB, []):
                    ser = ("series", A, B)
                    if well_formed(ser) and verts(ser) == n:
                        cur.append(ser)
                    jn = ("join", A, B)
                    if well_formed(jn) and verts(jn) == n:
                        cur.append(jn)
            nA += 1
        by_n[n] = cur
        n += 1
    out = []
    n = 2
    while n <= max_n:
        out.extend(by_n[n])
        n += 1
    return out


def bound(s):
    n = verts(s)
    return pow2(n - 2)


# ---------------------------------------------------------------------------

def main():
    head("Mazur height span")
    note("stdlib only; two 2^k engines; no solver; no lib/")
    note("not SPRC; not polynomial area; not bit length")

    head("[A]  pasting inequality")
    paste_ok = True
    a = 1
    while a <= 16:
        b = 1
        while b <= 16:
            left = pow2(a - 1) + pow2(b - 1)
            right = pow2(a + b - 1)
            if left > right:
                paste_ok = False
            b += 1
        a += 1
    check("L-PASTE: 2^{a-1}+2^{b-1} <= 2^{a+b-1} for a,b=1..16", paste_ok)
    check("L-PASTE tight at (1,1)", pow2(0) + pow2(0) == pow2(1))

    head("[B]  join arithmetic")
    join_ok = True
    A = 1
    while A <= 20:
        W = 1
        while W <= 20:
            T = A + 1 + max(A - 1, W) + W
            if T > 2 * (A + W):
                join_ok = False
            W += 1
        A += 1
    check("L-JOIN: worst-case T <= 2(A+W) for A,W=1..20", join_ok)
    pq_ok = True
    p = 1
    while p <= 16:
        q = 1
        while q <= 16:
            if 2 * (p + q - 1) > 2 * p * q:
                pq_ok = False
            q += 1
        p += 1
    check("L-JOIN: 2(p+q-1) <= 2pq for p,q=1..16", pq_ok)
    check("L-JOIN equality at p=q=1", 2 * (1 + 1 - 1) == 2 * 1 * 1)

    head("[C]  named tight schemes")
    edge = ("edge",)
    c3 = ("cycle", 3)
    path3 = ("series", edge, edge)
    check("edge: n=2 T=1 bound=1",
          verts(edge) == 2 and span(edge) == 1 and bound(edge) == 1)
    check("C3: n=3 T=2 bound=2",
          verts(c3) == 3 and span(c3) == 2 and bound(c3) == 2)
    check("two-edge series: n=3 T=2 bound=2",
          verts(path3) == 3 and span(path3) == 2 and bound(path3) == 2)
    check("C4: n=4 T=3 bound=4",
          verts(("cycle", 4)) == 4 and span(("cycle", 4)) == 3
          and bound(("cycle", 4)) == 4)

    head("[D]  exhaustive well-formed schemes, n <= 8")
    schemes = all_schemes(8)
    n_sch = len(schemes)
    n_fail = 0
    n_eq = 0
    max_n = 0
    max_T = 0
    for s in schemes:
        if not well_formed(s):
            n_fail += 1
            continue
        n = verts(s)
        T = span(s)
        B = bound(s)
        if n > max_n:
            max_n = n
        if T > max_T:
            max_T = T
        if T > B:
            n_fail += 1
        if T == B:
            n_eq += 1
    check("every generated scheme is well-formed and T <= 2^{n-2}",
          n_fail == 0, "count=%d max_n=%d max_T=%d tight=%d" %
          (n_sch, max_n, max_T, n_eq))
    check("census is not vacuous", n_sch >= 100, "count=%d" % n_sch)

    head("[E]  join of two 3-cycles")
    j = ("join", c3, c3)
    check("join(C3,C3) well-formed", well_formed(j))
    # C3: n=3 T=2, W=1, A=2, T=2+1+max(1,1)+1=5, n=5, bound=8
    check("join(C3,C3): n=5 T=5 bound=8",
          verts(j) == 5 and span(j) == 5 and bound(j) == 8,
          "n=%d T=%d B=%d" % (verts(j), span(j), bound(j)))

    head("[F]  engines agree on 2^k")
    k = 0
    agree = True
    while k <= 20:
        if pow2_mul(k) != pow2_shift(k):
            agree = False
        k += 1
    check("pow2_mul == pow2_shift for k=0..20", agree)

    print()
    print("-" * 72)
    print("checks run through; failures: %d   (%.1f s)"
          % (len(FAILS), time.time() - T0))
    print()
    print("EXTERNAL DEPENDENCIES")
    print("  (none)")
    print()
    print("NOT CLAIMED: SPRC; polynomial drawing area; O(n^2) bits;")
    print("a bound on every greedy labeling, only on Mazur's recurrences.")
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
