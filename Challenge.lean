import Mathlib

/-!
# Quantitative bounds for Mazur's greedy heights

Mazur (2026) proves the strong Papadimitriou–Ratajczak conjecture: every
finite simple 3-connected plane graph admits a convex greedy straight-line
drawing. The proof first builds injective integer heights with greedy
progress, then solves a Dirichlet problem for the horizontal coordinate.
The paper does not bound the heights or the bit length of the coordinates.

This note records four consequences of that construction's recurrences
and dart weights, not of the existence theorem, and not a construction
of a drawing or a common denominator.

1. The height span of the inductive recurrences is at most \(2^{n-2}\).
2. An integer matrix has \(|\det|\) at most the product of its row
   \(\ell^1\)-norms (Leibniz expansion). If every row \(\ell^1\)-norm is
   at most \(R\), then \(|\det|\le R^n\).
3. Mazur's dart weights, with heights in \(\{0,\ldots,T\}\), give
   one-sided neighbour sums at most \((n-1)T\) (the diagonal term vanishes
   and there are at most \(n-1\) other vertices). Interior Dirichlet rows
   then have \(\ell^1\)-norm at most \(2(n-1)^2T\); boundary rows are unit
   rows. Hence \(|\det M|\le(2(n-1)^2T)^n\) for \(n\ge 2\) and \(T\ge 1\).
4. Combining (1) and (3) bounds two candidate scaling expressions:
   \(T^2|\det M|\le 2^{n^2+n-4}(n-1)^{2n}\) and
   \(T^2|\det M|\,T\le 2^{n^2+2n-6}(n-1)^{2n}\). These are size bounds
   on those expressions. They do not prove that \(T^2|\det M|\) is a
   common denominator, that \(M\) is invertible, or that any integer
   drawing lies on a grid of that side.

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

/-- The height span of a well-formed Mazur scheme on n vertices is at
    most 2^{n-2}. -/
theorem span_le_two_pow (s : Scheme) (h : WellFormed s) :
    span s ≤ 2 ^ (verts s - 2) := by
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

end MazurSpan
