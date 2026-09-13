# Verification

Local checks, before any Palomar submit. Palomar's Comparator + NanoDa
run is Linux-side and is not duplicated here (no GitHub Actions; this
account is short of minutes).

## Lean

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build Span Challenge Solution
```

Expected: eleven `declaration uses sorry` warnings from
`Challenge.lean`. `Solution.lean` and `Span/` must be sorry-free.
Axioms used by the compared theorems are `propext`, `Classical.choice`,
`Quot.sound`.

## Python

```sh
python3 scripts/verify.py
python3 -O scripts/verify.py
```

Four stdlib censuses (no extra packages, no solver):

- `census_span.py` — well-formed schemes on \(n\le 8\); span vs
  \(2^{n-2}\) and vs the exact cap \(F(n)\).
- `census_bits.py` — Leibniz on small integer matrices; exponential
  identity at \(T=2^{n-2}\).
- `census_weights.py` — dart weights and Dirichlet rows on all
  undirected graphs and injective heights at \(n=3\) (384 matrices);
  two P/N engines, two det engines, two power engines.
- `census_exact.py` — exact \(F(n)\) through \(n=500\), bivariate
  join budgets through \(n=100\), dart-mass identities, and a K4
  adjugate example.

`check_source.py` rejects `sorry` / `axiom` / `native_decide` and
kernel-bypass options in `Span/` and `Solution.lean`.

## Not checked here

- SPRC.
- Invertibility of \(M\).
- That \(\Delta\neq 0\) in general, or that the adjugate vector is a
  unique Dirichlet solution without that hypothesis.
- A planar degree-budget grid theorem \(G\le 3^{2n-7}F(n)^n\). The
  Python census records the arithmetic of that expression; it is not
  a compared Lean theorem.
- That Mazur's constructed span equals the worst-case scheme span
  (the join uses \(c=1\), so the scheme span is an upper bound).
- Comparator against an adversarial Solution. That is Palomar's job
  after the repo is public.
