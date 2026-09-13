import Span.Basic
import Span.Bits
import Span.Weights

namespace Span

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

end Span
