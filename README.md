# md-lean

Bounds on **Mazur's height recurrences** and on two **candidate
scaling expressions** built from the Dirichlet matrix of that
construction. Not a proof of the strong Papadimitriou–Ratajczak
conjecture, and not a theorem that those expressions are a common
denominator or a grid size.

Mazur (public version 2026-09-09, announced on X 2026-09-12)
constructs injective integer heights and a Dirichlet horizontal
coordinate for a convex greedy drawing of a finite simple 3-connected
plane graph, and does not bound either. This repository records what
the recurrences and dart weights force for the height span \(T\) and
for \(|\det M|\), then multiplies those bounds.

**Audience.** Geometric graph theory / greedy embeddings: people who
already care about coordinate size in greedy drawings. This is a short
note on one construction's recurrences, not a new drawing algorithm.

**Start here.** The seven theorems and the definitions they use are in
[Challenge.lean](Challenge.lean) (Mathlib only, intentional `sorry`).
[Solution.lean](Solution.lean) proves the same names from `Span/`.
[DISCLOSURE.md](DISCLOSURE.md) is authorship.
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
4. **Scaling expressions.** Against (1) and (3),
   \(T^2|\det M|\le 2^{n^2+n-4}(n-1)^{2n}\) and
   \(T^2|\det M|\,T\le 2^{n^2+2n-6}(n-1)^{2n}\). These are bounds on
   those two products. They are the quantities one would clear if
   \(T^2|\det M|\) were a common denominator for Mazur's horizontal
   coordinates and if the vertical coordinates were then scaled by
   that factor; the Lean does not prove either of those hypotheses.

The factor \(n-1\) is the count of other vertices: the self-term
vanishes. Equality holds in the exponential arithmetic at
\(T=2^{n-2}\). At \(n=3\) the tight right-hand side for
\(T^2(2(n-1)^2T)^n\) is \(16384\); the looser \(n^{2n}\) form is
\(186624\).

Lean names: `MazurSpan.span_le_two_pow`,
`natAbs_det_le_prod_rowSum`, `natAbs_det_le_of_rowSum_le`,
`dirichlet_rowSum_le`, `dirichlet_det_le`, `coord_denom`,
`coord_grid`.

## What is not claimed

- SPRC, or any existence theorem for greedy drawings.
- That \(T^2|\det M|\) is a common denominator, or that scaling by it
  produces integer coordinates on a grid of side
  \(2^{n^2+2n-6}(n-1)^{2n}\).
- Invertibility of the Dirichlet matrix (Mazur's maximum principle).
- Polynomial grid area.
- That every greedy labeling obeys the span bound — only Mazur's
  recurrences, with worst-case join attachment.

## Prior grid-size and bit-complexity work

The compared theorems are about Mazur's height recurrences and the
Dirichlet matrix of that construction. They are not a drawing-area
theorem. The surrounding question is nevertheless the one asked for
Euclidean greedy drawings of 3-connected planar graphs: how many bits
do the coordinates need?

Leighton and Moitra (FOCS 2008; Discrete Comput. Geom. 44 (2010))
proved that every 3-connected planar graph has a Euclidean greedy
embedding. Those embeddings need not be planar, and representing their
coordinates has been analysed as using \(\Omega(n\log n)\) bits
(He–Zhang, SODA 2011). Angelini, Di Battista, and Frati independently
gave a constructive greedy embedding, again not a planar convex grid
drawing.

Succinct *Euclidean convex* greedy drawings are a different question.
He and Zhang (SODA 2011) showed that Schnyder drawings of triangulations
are greedy for a metric equivalent to Euclidean distance and use two
integer coordinates in \(\{0,\ldots,2n-5\}\) — polynomial grid, \(O(\log n)\)
bits — but that metric is not the Euclidean metric of the strong
conjecture. They also record that requiring Euclidean convex greediness
together with succinct coordinates fails in general.

Whether every 3-connected planar graph has a *planar* Euclidean greedy
drawing on a polynomial-size grid is open. Cao, Strelzoff, and Sun
claimed a negative answer for a family of subdivisions, with
\(2^{\Omega(n)}\) area and hence \(\Omega(n)\)-bit coordinates. Da Lozzo,
D'Angelo, and Frati (GD 2020, arXiv:2003.00556) showed that every
\(n\)-vertex graph in that family actually has a convex angle-monotone
(hence greedy) drawing on an \(O(n)\times O(n)\) grid, reopening the
polynomial-grid question, and proved the same grid bound for Halin
graphs. They also showed that some \(\alpha\)-Schnyder drawings with
fixed \(\alpha<60^\circ\) require exponential area.

Mazur's construction is Euclidean and convex, so it sits in the class
for which a polynomial grid is still open. The bounds here, if they
were grid sizes, would be \(2^{O(n^2)}\) — exponential area, \(O(n^2)\)
bits — and would not settle that question either way. They apply only
to the height span and to \(|\det M|\) of Mazur's weighted Laplacian,
and only after treating \(T^2|\det M|\) and \(T^2|\det M|\,T\) as
expressions to be bounded, not as a constructed grid.

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
