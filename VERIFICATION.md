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

Expected: seven `declaration uses sorry` warnings from
`Challenge.lean`. `Solution.lean` and `Span/` must be sorry-free.
Axioms used by the compared theorems are `propext`, `Classical.choice`,
`Quot.sound`.

## Python

```sh
python3 scripts/verify.py
python3 -O scripts/verify.py
```

Three stdlib censuses (no extra packages, no solver):

- `census_span.py` — well-formed schemes on \(n\le 8\); span vs
  \(2^{n-2}\).
- `census_bits.py` — Leibniz on small integer matrices; exponential
  identity at \(T=2^{n-2}\).
- `census_weights.py` — dart weights and Dirichlet rows on all
  undirected graphs and injective heights at \(n=3\) (384 matrices);
  two P/N engines, two det engines, two power engines.

`check_source.py` rejects `sorry` / `axiom` / `native_decide` and
kernel-bypass options in `Span/` and `Solution.lean`.

## Not checked here

- SPRC.
- Invertibility of \(M\).
- That Mazur's constructed span equals the worst-case scheme span
  (the join uses \(c=1\), so the scheme span is an upper bound).
- Comparator against an adversarial Solution. That is Palomar's job
  after the repo is public.
