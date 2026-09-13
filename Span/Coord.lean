import Span.Basic
import Span.Bits
import Span.Weights

namespace Span

open Matrix

/-- Clearing \(T^2|\det M|\) once the Dirichlet matrix is built from
    Mazur's weights and the heights sit in \(\{0,\ldots,T\}\). -/
theorem coord_denom {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hn : 2 ≤ n) (hTpos : 1 ≤ T) (hT : T ≤ 2 ^ (n - 2))
    (hh : ∀ i, h i ≤ T) :
    T ^ 2 * (dirichlet Adj h B).det.natAbs ≤
      2 ^ (n ^ 2 + n - 4) * (n - 1) ^ (2 * n) :=
  clearing_denom_le_pred hn hT (dirichlet_det_le Adj h B hh hn hTpos)

theorem coord_grid {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hn : 2 ≤ n) (hTpos : 1 ≤ T) (hT : T ≤ 2 ^ (n - 2))
    (hh : ∀ i, h i ≤ T) :
    T ^ 2 * (dirichlet Adj h B).det.natAbs * T ≤
      2 ^ (n ^ 2 + 2 * n - 6) * (n - 1) ^ (2 * n) :=
  clearing_grid_le_pred hn hT (dirichlet_det_le Adj h B hh hn hTpos)

/-- Glue: a well-formed scheme's span supplies \(T\), and the
    Dirichlet matrix built from any height labeling bounded by that
    span obeys the denominator bound. -/
theorem coord_denom_of_scheme (sch : Scheme) (hwf : WellFormed sch)
    (Adj : Fin (verts sch) → Fin (verts sch) → Bool)
    (h : Fin (verts sch) → ℕ) (B : Finset (Fin (verts sch)))
    (hh : ∀ i, h i ≤ span sch) :
    (span sch) ^ 2 * (dirichlet Adj h B).det.natAbs ≤
      2 ^ (verts sch ^ 2 + verts sch - 4) *
        (verts sch - 1) ^ (2 * verts sch) :=
  coord_denom Adj h B (two_le_verts sch) (one_le_span sch)
    (span_le_two_pow sch hwf) hh

theorem coord_grid_of_scheme (sch : Scheme) (hwf : WellFormed sch)
    (Adj : Fin (verts sch) → Fin (verts sch) → Bool)
    (h : Fin (verts sch) → ℕ) (B : Finset (Fin (verts sch)))
    (hh : ∀ i, h i ≤ span sch) :
    (span sch) ^ 2 * (dirichlet Adj h B).det.natAbs * span sch ≤
      2 ^ (verts sch ^ 2 + 2 * verts sch - 6) *
        (verts sch - 1) ^ (2 * verts sch) :=
  coord_grid Adj h B (two_le_verts sch) (one_le_span sch)
    (span_le_two_pow sch hwf) hh

/-- Quadratic boundary values for Mazur's Dirichlet problem, unscaled by
    \(T^2\). Interior coordinates are zero on the right-hand side. -/
def boundaryTarget (h : Fin n → ℕ) (T : ℕ) (B : Finset (Fin n)) : Fin n → ℤ :=
  fun s => if s ∈ B then (h s * (T - h s) : ℤ) else 0

lemma dirichlet_mulVec_adjugate (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (u : Fin n → ℤ) :
    (dirichlet Adj h B) *ᵥ ((dirichlet Adj h B).adjugate *ᵥ u) =
      (dirichlet Adj h B).det • u := by
  set M := dirichlet Adj h B
  calc
    M *ᵥ (M.adjugate *ᵥ u) = (M * M.adjugate) *ᵥ u := mulVec_mulVec u M M.adjugate
    _ = (M.det • (1 : Matrix (Fin n) (Fin n) ℤ)) *ᵥ u := by rw [mul_adjugate]
    _ = M.det • ((1 : Matrix (Fin n) (Fin n) ℤ) *ᵥ u) := smul_mulVec _ _ _
    _ = M.det • u := by rw [one_mulVec]

lemma dirichlet_mulVec_of_mem_boundary (Adj : Fin n → Fin n → Bool)
    (h : Fin n → ℕ) (B : Finset (Fin n)) {s : Fin n} (hs : s ∈ B)
    (z : Fin n → ℤ) :
    ((dirichlet Adj h B) *ᵥ z) s = z s := by
  simp [mulVec, dotProduct, dirichlet, hs]

/-- The adjugate supplies an integer vector \(z\) with \(Mz=\Delta u\). On
    the boundary this is \(z_s=\Delta h_s(T-h_s)\). Invertibility of \(M\)
    is not claimed; if \(\Delta=0\) the identity is \(0=0\). -/
theorem dirichlet_adjugate_clears (Adj : Fin n → Fin n → Bool)
    (h : Fin n → ℕ) (B : Finset (Fin n)) (T : ℕ) :
    let M := dirichlet Adj h B
    let u := boundaryTarget h T B
    let z := M.adjugate *ᵥ u
    M *ᵥ z = M.det • u ∧
      ∀ s ∈ B, z s = M.det * (h s * (T - h s) : ℤ) := by
  intro M u z
  refine ⟨dirichlet_mulVec_adjugate Adj h B u, ?_⟩
  intro s hs
  have hrow := dirichlet_mulVec_of_mem_boundary Adj h B hs z
  have hmul : (M *ᵥ z) s = (M.det • u) s := by
    rw [dirichlet_mulVec_adjugate]
  have : z s = (M.det • u) s := by
    rw [← hrow, hmul]
  simpa [u, boundaryTarget, hs, Pi.smul_apply, smul_eq_mul] using this

end Span
