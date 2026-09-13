import Mathlib

/-!
# Quantitative bounds for Mazur's greedy heights

Mazur (2026) proves the strong Papadimitriou–Ratajczak conjecture: every
finite simple 3-connected plane graph admits a convex greedy straight-line
drawing. The proof first builds injective integer heights with greedy
progress, then solves a Dirichlet problem for the horizontal coordinate.
The paper does not bound the heights or the bit length of the coordinates.

This note records consequences of that construction's recurrences
and dart weights, not of the existence theorem, and not a construction
of a drawing.

1. For a well-formed scheme on \(n\) vertices with \(j\) nontrivial
   joins, \(T+1\le 2^j(n-2j)\). Every admissible pair
   \((n,j)=(2,0)\) or \(2j+3\le n\) is attained. The one-parameter
   maximum is \(F(n)=2^{n/2}-1\) (\(n\) even) or
   \(3\cdot 2^{(n-3)/2}-1\) (\(n\) odd). The coarser bound
   \(T\le 2^{n-2}\) remains as a corollary.
2. An integer matrix has \(|\det|\) at most the product of its row
   \(\ell^1\)-norms (Leibniz expansion). If every row \(\ell^1\)-norm is
   at most \(R\), then \(|\det|\le R^n\).
3. Mazur's dart weights, with heights in \(\{0,\ldots,T\}\), give
   one-sided neighbour sums at most \((n-1)T\) (the diagonal term vanishes
   and there are at most \(n-1\) other vertices). Interior Dirichlet rows
   then have \(\ell^1\)-norm at most \(2(n-1)^2T\); boundary rows are unit
   rows. Hence \(|\det M|\le(2(n-1)^2T)^n\) for \(n\ge 2\) and \(T\ge 1\).
   Locally, the interior outgoing dart-weight sum is at most
   \(a_s b_s T\). On the boundary the Dirichlet row is a unit row, and
   the algebraic mass \(a_s N_s+b_s P_s\) need not equal the dart-weight
   sum (boundary darts have weight one).
4. Combining the coarser span bound and (3) bounds two candidate scaling
   expressions: \(T^2|\det M|\le 2^{n^2+n-4}(n-1)^{2n}\) and
   \(T^2|\det M|\,T\le 2^{n^2+2n-6}(n-1)^{2n}\). These are size bounds
   on those expressions.
5. Independently of invertibility, the adjugate identity produces an
   integer vector \(z=\operatorname{adj}(M)u\) with \(Mz=\Delta u\) and
   \(z_s=\Delta h_s(T-h_s)\) on the boundary. If \(\Delta\neq 0\), this
   is an integer clearing of Mazur's quadratic boundary values; the
   compared statement does not prove \(\Delta\neq 0\).

The factor \(n-1\) is the graph-theoretic count of other vertices, not a
change of Mazur's recipe. Polynomial grid area is not claimed.

This Mathlib-only file intentionally contains `sorry` placeholders.
The corresponding declarations are proved in `Solution.lean`, which
does not import this file.
-/

namespace MazurSpan

/-- A rooted piece in Mazur's inductive construction of greedy heights. -/
inductive Scheme where
  | edge : Scheme
  | cycle (k : ℕ) : Scheme
  | series (A B : Scheme) : Scheme
  | join (H K : Scheme) : Scheme

open Scheme

/-- Vertex count of a rooted piece. A cycle parameter `k` means `k+3`
    vertices, so every cycle has at least three vertices. -/
def verts : Scheme → ℕ
  | edge => 2
  | cycle k => k + 3
  | series A B => verts A + verts B - 1
  | join H K => verts H + verts K - 1

/-- Height span produced by the recurrences. On a join, the attachment
    height `c` is taken in the worst case `c = 1`. -/
def span : Scheme → ℕ
  | edge => 1
  | cycle k => k + 2
  | series A B => span A + span B
  | join H K =>
      let A := span H
      let W := span K - 1
      if W = 0 then A + 1 else A + 1 + max (A - 1) W + W

/-- Joins with a nontrivial upper chain require at least three vertices
    on each side, matching the paper's distinct roots `u,a,z`. -/
def WellFormed : Scheme → Prop
  | edge => True
  | cycle _ => True
  | series A B => WellFormed A ∧ WellFormed B
  | join H K =>
      WellFormed H ∧ WellFormed K ∧
      (span K = 1 → verts K = 2) ∧
      (1 < span K → 3 ≤ verts H ∧ 3 ≤ verts K)

/-- Number of nontrivial joins: a join whose upper child has span > 1. -/
def joinCount : Scheme → ℕ
  | .edge => 0
  | .cycle _ => 0
  | .series A B => joinCount A + joinCount B
  | .join H K =>
      joinCount H + joinCount K + if 1 < span K then 1 else 0

/-- Exact one-parameter maximum of the scheme grammar. -/
def exactCap (n : ℕ) : ℕ :=
  if n % 2 = 0 then 2 ^ (n / 2) - 1 else 3 * 2 ^ ((n - 3) / 2) - 1

/-- The height span of a well-formed Mazur scheme on n vertices is at
    most 2^{n-2}. A coarser corollary of `span_le_exact`. -/
theorem span_le_two_pow (s : Scheme) (h : WellFormed s) :
    span s ≤ 2 ^ (verts s - 2) := by
  sorry

/-- Exact one-parameter maximum: \(T\le F(n)\). -/
theorem span_le_exact (s : Scheme) (h : WellFormed s) :
    span s ≤ exactCap (verts s) := by
  sorry

/-- Every value \(F(n)\) is attained by some well-formed scheme. -/
theorem exists_span_eq_exact (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Scheme, WellFormed s ∧ verts s = n ∧ span s = exactCap n := by
  sorry

/-- Two-parameter budget: \(T+1\le 2^j(n-2j)\) for every well-formed
    scheme. -/
theorem span_succ_le_join_budget (s : Scheme) (h : WellFormed s) :
    span s + 1 ≤ 2 ^ joinCount s * (verts s - 2 * joinCount s) := by
  sorry

/-- Attainment at every admissible pair: \((n,j)=(2,0)\) or
    \(2j+3\le n\). -/
theorem exists_span_eq_join_budget (n j : ℕ)
    (h : n = 2 ∧ j = 0 ∨ 2 * j + 3 ≤ n) :
    ∃ s : Scheme, WellFormed s ∧ verts s = n ∧ joinCount s = j ∧
      span s + 1 = 2 ^ j * (n - 2 * j) := by
  sorry

/-- The `(i, j)`-entry of an integer matrix. Named so compared
    statements do not apply a `Matrix` as a function; Palomar's
    core notation audit treats `Matrix` as an opaque type. -/
def entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℤ :=
  A i j

/-- An integer matrix has |det| at most the product of its row ℓ¹-norms. -/
theorem natAbs_det_le_prod_rowSum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    A.det.natAbs ≤ ∏ i : Fin n, ∑ j : Fin n, (entry A i j).natAbs := by
  sorry

/-- If every row ℓ¹-norm is at most R, then |det| ≤ R^n. -/
theorem natAbs_det_le_of_rowSum_le {n R : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i, ∑ j, (entry A i j).natAbs ≤ R) :
    A.det.natAbs ≤ R ^ n := by
  sorry

variable {n : ℕ}

/-- Upward neighbour sum \(P_s = \sum_{t\sim s}\max\{h(t)-h(s),0\}\). -/
def upwardSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then h t - h s else 0

/-- Downward neighbour sum \(N_s = \sum_{t\sim s}\max\{h(s)-h(t),0\}\). -/
def downwardSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then h s - h t else 0

/-- Mazur's directed dart weight. Boundary vertices are not used as
    Laplacian sources: the Dirichlet matrix places unit rows there. -/
def dartWeight (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (s t : Fin n) : ℕ :=
  if s = t then 0
  else if Adj s t = false then 0
  else if s ∈ B then 1
  else if h s < h t then downwardSum Adj h s
  else if h t < h s then upwardSum Adj h s
  else 0

/-- Dirichlet matrix: unit rows on the boundary, weighted Laplacian
    on the interior, matching Mazur §3. -/
def dirichlet (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun s t =>
    if s ∈ B then (if s = t then 1 else 0)
    else if s = t then ∑ u : Fin n, (dartWeight Adj h B s u : ℤ)
    else - (dartWeight Adj h B s t : ℤ)

/-- Every row of the Dirichlet matrix has ℓ¹-norm at most \(2(n-1)^2T\). -/
theorem dirichlet_rowSum_le {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hh : ∀ i, h i ≤ T) (hn : 2 ≤ n) (hT : 1 ≤ T) (s : Fin n) :
    ∑ t, (entry (dirichlet Adj h B) s t).natAbs ≤ 2 * (n - 1) ^ 2 * T := by
  sorry

/-- Hence \(|\det M|\le(2(n-1)^2T)^n\). -/
theorem dirichlet_det_le {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hh : ∀ i, h i ≤ T) (hn : 2 ≤ n) (hT : 1 ≤ T) :
    (dirichlet Adj h B).det.natAbs ≤ (2 * (n - 1) ^ 2 * T) ^ n := by
  sorry

/-- Bound on the candidate scaling \(T^2|\det M|\), not a denominator theorem. -/
theorem coord_denom {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hn : 2 ≤ n) (hTpos : 1 ≤ T) (hT : T ≤ 2 ^ (n - 2))
    (hh : ∀ i, h i ≤ T) :
    T ^ 2 * (dirichlet Adj h B).det.natAbs ≤
      2 ^ (n ^ 2 + n - 4) * (n - 1) ^ (2 * n) := by
  sorry

/-- Bound on the candidate scaling \(T^2|\det M|\,T\), not a grid-drawing theorem. -/
theorem coord_grid {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hn : 2 ≤ n) (hTpos : 1 ≤ T) (hT : T ≤ 2 ^ (n - 2))
    (hh : ∀ i, h i ≤ T) :
    T ^ 2 * (dirichlet Adj h B).det.natAbs * T ≤
      2 ^ (n ^ 2 + 2 * n - 6) * (n - 1) ^ (2 * n) := by
  sorry

/-- Neighbours of `s` with strictly larger height. -/
def higherCount (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then (if h s < h t then 1 else 0) else 0

/-- Neighbours of `s` with strictly smaller height. -/
def lowerCount (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then (if h t < h s then 1 else 0) else 0

/-- Algebraic dart mass \(\delta_s=a_s N_s+b_s P_s\). On the interior
    this equals the sum of outgoing `dartWeight`s; on the boundary it
    need not. -/
def dartMass (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  higherCount Adj h s * downwardSum Adj h s +
    lowerCount Adj h s * upwardSum Adj h s

/-- Algebraic mass bound \(\delta_s\le a_s b_s T\), at every vertex. -/
theorem dartMass_le {n T : ℕ} (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (hh : ∀ i, h i ≤ T) (s : Fin n) :
    dartMass Adj h s ≤ higherCount Adj h s * lowerCount Adj h s * T := by
  sorry

/-- Interior outgoing dart-weight sum equals the algebraic dart mass. -/
theorem dartWeight_sum_eq_dartMass {n : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    {s : Fin n} (hs : s ∉ B) :
    ∑ t, dartWeight Adj h B s t = dartMass Adj h s := by
  sorry

/-- Interior outgoing dart-weight sum is at most \(a_s b_s T\). -/
theorem dartWeight_interior_sum_le {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hh : ∀ i, h i ≤ T) {s : Fin n} (hs : s ∉ B) :
    ∑ t, dartWeight Adj h B s t ≤
      higherCount Adj h s * lowerCount Adj h s * T := by
  sorry

/-- Quadratic boundary values, unscaled by \(T^2\). -/
def boundaryTarget (h : Fin n → ℕ) (T : ℕ) (B : Finset (Fin n)) : Fin n → ℤ :=
  fun s => if s ∈ B then (h s * (T - h s) : ℤ) else 0

/-- Adjugate identity: \(Mz=\Delta u\) and \(z_s=\Delta h_s(T-h_s)\) on
    the boundary. Does not prove invertibility. -/
theorem dirichlet_adjugate_clears {n : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (T : ℕ) :
    let M := dirichlet Adj h B
    let u := boundaryTarget h T B
    let z := M.adjugate.mulVec u
    M.mulVec z = M.det • u ∧
      ∀ s ∈ B, z s = M.det * (h s * (T - h s) : ℤ) := by
  sorry

end MazurSpan
