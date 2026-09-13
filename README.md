# md-lean

Quantitative bounds for **Mazur's greedy heights**, not a proof of the
strong Papadimitriou–Ratajczak conjecture.

Mazur (public version 2026-09-09, announced on X 2026-09-12) constructs
injective integer heights and a Dirichlet horizontal coordinate for a
convex greedy drawing of a finite simple 3-connected plane graph, and
does not bound either. This repository records what those recurrences
and weights force: height span \(T\le 2^{n-2}\), then a common
denominator \(Q\le 2^{n^2+n-4}(n-1)^{2n}\) for the scaled integer
drawing.

**Audience.** Geometric graph theory / greedy embeddings: people who
already care about coordinate size in greedy drawings. This is a short
note on one construction, not a new drawing algorithm.

**Start here.** The seven theorems and the definitions they use are in
[Challenge.lean](Challenge.lean) (158 lines, Mathlib only, intentional
`sorry`). [Solution.lean](Solution.lean) proves the same names from
`Span/`. [DISCLOSURE.md](DISCLOSURE.md) is authorship.
[VERIFICATION.md](VERIFICATION.md) is how to replay the checks.

## What is proved

Let \(n\ge 2\) be the number of vertices of a well-formed Mazur scheme
(edge, cycle, binary series, two-range join with worst-case attachment
height \(c=1\)).

1. **Span.** The height span of the scheme is at most \(2^{n-2}\).
2. **Leibniz.** An integer matrix has \(|\det|\) at most the product of
   its row \(\ell^1\)-norms. If every row \(\ell^1\)-norm is at most
   \(R\), then \(|\det|\le R^n\).
3. **Weights.** Heights in \(\{0,\ldots,T\}\) give one-sided neighbour
   sums at most \((n-1)T\). Interior Dirichlet rows then have
   \(\ell^1\)-norm at most \(2(n-1)^2T\); boundary rows are unit rows.
   Hence \(|\det M|\le(2(n-1)^2T)^n\) when \(T\ge 1\).
4. **Clearing.** Against (1) and (3),
   \(Q=T^2|\det M|\le 2^{n^2+n-4}(n-1)^{2n}\). After scaling by \(Q\),
   integer coordinates lie on a grid of side
   \(2^{n^2+2n-6}(n-1)^{2n}\).

The factor \(n-1\) is the count of other vertices: the self-term
vanishes. Equality holds in the exponential arithmetic at
\(T=2^{n-2}\). At \(n=3\) the tight right-hand side is \(16384\); the
looser \(n^{2n}\) form is \(186624\).

Lean names: `MazurSpan.span_le_two_pow`,
`natAbs_det_le_prod_rowSum`, `natAbs_det_le_of_rowSum_le`,
`dirichlet_rowSum_le`, `dirichlet_det_le`, `coord_denom`,
`coord_grid`.

## What is not claimed

- SPRC, or any existence theorem for greedy drawings.
- Polynomial grid area, or a bit-length bound sharper than this common
  denominator.
- Invertibility of the Dirichlet matrix (Mazur's maximum principle).
- That every greedy labeling obeys the span bound — only Mazur's
  recurrences, with worst-case join attachment.
- Historical novelty of the corollary. Mazur's paper does not state
  these bounds. This file does not survey the greedy-drawing literature
  for earlier bit-length estimates.

## Source

- Lech Mazur, *A Proof of the Strong Papadimitriou–Ratajczak
  Conjecture*, public version 2026-09-09.
  [ProofAtlas page](https://proofatlas.ai/formalizations/strong-papadimitriou-ratajczak-conjecture/),
  [PDF](https://proofatlas.ai/papers/strong-papadimitriou-ratajczak-conjecture/Strong_Papadimitriou_Ratajczak_Conjecture_Proof_2026-09-09.pdf).
- Author announcement: [@LechMazur, 2026-09-12](https://x.com/LechMazur/status/2098915169799733339).
- ProofAtlas records the accompanying existence Lean as pending
  accepted-result publication. That Lean is not imported here.

## Files

| File | Role |
|------|------|
| `Challenge.lean` | Statement surface. Audit this. |
| `Solution.lean` | Same names, proved from `Span/`. Does not import Challenge. |
| `Span/` | Span recurrences, Leibniz det, dart weights, glue. |
| `scripts/verify.py` | Stdlib censuses (span schemes, det arithmetic, weights) plus a source guard. |
| `formalization.yaml` | Palomar metadata. |
| `comparator.json` | Challenge/Solution comparison list. |

No GitHub Actions. Palomar runs Comparator on submit.

## Verify

Toolchain: Lean `v4.33.0`, Mathlib `v4.33.0` (commit `db584cd6…` in
`lake-manifest.json`). Elan on `PATH`:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
python3 scripts/verify.py
python3 -O scripts/verify.py
```

`lake build` is expected to print seven `declaration uses sorry`
warnings from Challenge and nothing else. `scripts/verify.py` must
print `VERIFY GREEN` under both runners.

License: [MIT](LICENSE).
