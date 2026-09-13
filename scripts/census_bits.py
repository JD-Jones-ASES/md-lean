#!/usr/bin/env python3
# -*- coding: ascii -*-
"""
CLEARING MAZUR'S DIRICHLET DENOMINATOR.

THEOREMS
--------
  (L-L1DET) For an n x n integer matrix, |det| <= product of
      the row ell_1 norms.  Leibniz expansion: the permutation
      terms are a subset of the expansion of the product of
      row sums.

  (L-ROW) If every row ell_1-norm is <= R then
      |det| <= R^n.

  (T-DENOM) If n >= 2, T <= 2^{n-2}, and
      d <= (2 n^2 T)^n, then
      T^2 * d <= 2^{n^2 + n - 4} * n^{2n}.

  (T-QT) Under the same hypotheses,
      T^2 * d * T <= 2^{n^2 + 2n - 6} * n^{2n}.

EXTERNAL INPUTS
---------------
  None.  The Dirichlet row-sum bound 2 n^2 T is Mazur Sec. 3,
  used here only as the hypothesis d <= (2 n^2 T)^n.
  Span T <= 2^{n-2} is the companion span census.

HONESTY
-------
 (1) Desk: Grok 4.6, 2026-09-13.  Not SPRC, not polynomial area.
 (2) Two det engines on the 2x2 and 3x3 censuses (permutation
     expansion vs closed form / cofactor).
 (3) Two power engines.
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


def pow2(k):
    return 1 << k


def ipow(a, e):
    """Nonnegative integer power, iterative."""
    x = 1
    i = 0
    while i < e:
        x *= a
        i += 1
    return x


def ipow2(a, e):
    """Second engine: binary exponentiation."""
    x = 1
    b = a
    k = e
    while k > 0:
        if k & 1:
            x *= b
        b *= b
        k >>= 1
    return x


def perms(n):
    return itertools.permutations(range(n))


def det_perm(A):
    """Permutation expansion.  A is n x n nested lists of ints."""
    n = len(A)
    total = 0
    for p in perms(n):
        sign = 1
        seen = []
        # sign from inversion count
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


def det_2x2(A):
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]


def det_3x3(A):
    a, b, c = A[0]
    d, e, f = A[1]
    g, h, i = A[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def row_l1(A):
    out = []
    for row in A:
        s = 0
        for x in row:
            if x < 0:
                s += -x
            else:
                s += x
        out.append(s)
    return out


def prod_list(xs):
    p = 1
    for x in xs:
        p *= x
    return p


def abs_z(x):
    if x < 0:
        return -x
    return x


# ---------------------------------------------------------------------------

def main():
    head("Dirichlet denominator bits")
    note("stdlib only; two det engines; two power engines")
    note("not SPRC; not polynomial area")

    head("[A]  power engines agree")
    agree = True
    a = 0
    while a <= 8:
        e = 0
        while e <= 8:
            if ipow(a, e) != ipow2(a, e):
                agree = False
            e += 1
        a += 1
    check("ipow == binary exp for a,e = 0..8", agree)

    head("[B]  2x2 ell_1-Hadamard, entries in [-2,2]")
    n_fail = 0
    n_tot = 0
    n_eq = 0
    for vals in itertools.product(range(-2, 3), repeat=4):
        A = [[vals[0], vals[1]], [vals[2], vals[3]]]
        d1 = det_perm(A)
        d2 = det_2x2(A)
        n_tot += 1
        if d1 != d2:
            n_fail += 1
            continue
        R = prod_list(row_l1(A))
        ad = abs_z(d1)
        if ad > R:
            n_fail += 1
        if ad == R:
            n_eq += 1
    check("2x2: perm det = ad-bc", n_fail == 0, "n=%d" % n_tot)
    check("2x2: |det| <= product of row ell_1", n_fail == 0,
          "tight=%d / %d" % (n_eq, n_tot))

    head("[C]  3x3 ell_1-Hadamard, entries in {-1,0,1}")
    n_fail = 0
    n_tot = 0
    n_eq = 0
    for vals in itertools.product((-1, 0, 1), repeat=9):
        A = [[vals[0], vals[1], vals[2]],
             [vals[3], vals[4], vals[5]],
             [vals[6], vals[7], vals[8]]]
        d1 = det_perm(A)
        d2 = det_3x3(A)
        n_tot += 1
        if d1 != d2:
            n_fail += 1
            continue
        R = prod_list(row_l1(A))
        ad = abs_z(d1)
        if ad > R:
            n_fail += 1
        if ad == R:
            n_eq += 1
    check("3x3: perm det = cofactor", n_fail == 0, "n=%d" % n_tot)
    check("3x3: |det| <= product of row ell_1", n_fail == 0,
          "tight=%d / %d" % (n_eq, n_tot))

    head("[D]  T^2 d bound, n=2..10, T=1 and T=2^{n-2}")
    denom_ok = True
    qt_ok = True
    n = 2
    while n <= 10:
        Tmax = pow2(n - 2)
        for T in (1, Tmax):
            cap = ipow(2 * n * n * T, n)
            left = ipow(T, 2) * cap
            # exponent n^2 + n - 4
            exp = n * n + n - 4
            right = pow2(exp) * ipow(n, 2 * n)
            if left > right:
                denom_ok = False
            leftQT = left * T
            expQT = n * n + 2 * n - 6
            rightQT = pow2(expQT) * ipow(n, 2 * n)
            if leftQT > rightQT:
                qt_ok = False
        n += 1
    check("T-DENOM: T^2 (2 n^2 T)^n <= 2^{n^2+n-4} n^{2n}", denom_ok)
    check("T-QT: T^3 (2 n^2 T)^n <= 2^{n^2+2n-6} n^{2n}", qt_ok)

    head("[E]  identity T^{n+2} * 2^n = 2^{n^2+n-4} n^{2n} / n^{2n} * ...")
    # At T = 2^{n-2}: T^2 (2 n^2 T)^n = 2^n n^{2n} T^{n+2}
    # = 2^n n^{2n} 2^{(n-2)(n+2)} = 2^{n + n^2 - 4} n^{2n}
    ident_ok = True
    n = 2
    while n <= 8:
        T = pow2(n - 2)
        left = ipow(T, 2) * ipow(2 * n * n * T, n)
        right = pow2(n * n + n - 4) * ipow(n, 2 * n)
        if left != right:
            ident_ok = False
        n += 1
    check("equality at the span endpoint T=2^{n-2}, n=2..8", ident_ok)

    head("[F]  n=1 is excluded: exponent n^2+n-4 = -2")
    check("n=2 exponent is 2", 2 * 2 + 2 - 4 == 2)

    print()
    print("-" * 72)
    print("checks run through; failures: %d   (%.1f s)"
          % (len(FAILS), time.time() - T0))
    print()
    print("EXTERNAL DEPENDENCIES")
    print("  span census for T <= 2^{n-2} (not consumed as a number here)")
    print("  Mazur Sec. 3 for the shape d <= (2 n^2 T)^n (hypothesis)")
    print()
    print("NOT CLAIMED: SPRC; polynomial area; that every greedy")
    print("labeling obeys the bound; bit length of a reduced fraction")
    print("sharper than this common-denominator bound.")
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
