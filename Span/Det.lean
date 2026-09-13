import Mathlib

namespace Span

open Matrix Finset

theorem natAbs_det_le_prod_rowSum :
    ∀ n, ∀ (A : Matrix (Fin n) (Fin n) ℤ),
      A.det.natAbs ≤ ∏ i : Fin n, ∑ j : Fin n, (A i j).natAbs
  | 0, A => by
      simp [Matrix.det_fin_zero]
  | n + 1, A => by
      have ih := natAbs_det_le_prod_rowSum n
      set z : Fin (n + 1) := 0
      rw [Matrix.det_succ_row_zero]
      have hterm : ∀ j : Fin (n + 1),
          ((-1 : ℤ) ^ (j : ℕ) * A z j *
              det (A.submatrix Fin.succ j.succAbove)).natAbs =
            (A z j).natAbs *
              (det (A.submatrix Fin.succ j.succAbove)).natAbs := by
        intro j
        rw [mul_assoc, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
        simp
      have hsum :
          (∑ j : Fin (n + 1),
              ((-1 : ℤ) ^ (j : ℕ) * A z j *
                det (A.submatrix Fin.succ j.succAbove))).natAbs ≤
            ∑ j : Fin (n + 1),
              (A z j).natAbs *
                (det (A.submatrix Fin.succ j.succAbove)).natAbs := by
        refine (Int.natAbs_sum_le _ _).trans ?_
        gcongr with j
        exact (hterm j).le
      refine hsum.trans ?_
      have hdrop : ∀ j r : Fin (n + 1),
          ∑ k : Fin n, (A r (j.succAbove k)).natAbs ≤
            ∑ k : Fin (n + 1), (A r k).natAbs := by
        intro j r
        have hsplit := Fin.sum_univ_succAbove (fun k => (A r k).natAbs) j
        have : (A r j).natAbs + ∑ k : Fin n, (A r (j.succAbove k)).natAbs =
            ∑ k, (A r k).natAbs := hsplit.symm
        omega
      have hih : ∀ j : Fin (n + 1),
          (det (A.submatrix Fin.succ j.succAbove)).natAbs ≤
            ∏ i : Fin n, ∑ k : Fin (n + 1), (A i.succ k).natAbs := by
        intro j
        have := ih (A.submatrix Fin.succ j.succAbove)
        refine this.trans ?_
        gcongr with i
        simpa [Matrix.submatrix_apply] using hdrop j i.succ
      have hstep :
          ∑ j : Fin (n + 1),
              (A z j).natAbs *
                (det (A.submatrix Fin.succ j.succAbove)).natAbs ≤
            ∑ j : Fin (n + 1),
              (A z j).natAbs *
                ∏ i : Fin n, ∑ k : Fin (n + 1), (A i.succ k).natAbs := by
        gcongr with j
        exact hih j
      refine hstep.trans ?_
      have hfact :
          ∑ j : Fin (n + 1),
              (A z j).natAbs *
                ∏ i : Fin n, ∑ k : Fin (n + 1), (A i.succ k).natAbs =
            (∑ j : Fin (n + 1), (A z j).natAbs) *
              ∏ i : Fin n, ∑ k : Fin (n + 1), (A i.succ k).natAbs := by
        exact (Finset.sum_mul _ _ _).symm
      rw [hfact, Fin.prod_univ_succ (fun i => ∑ j, (A i j).natAbs)]

theorem natAbs_det_le_of_rowSum_le {n R : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i, ∑ j, (A i j).natAbs ≤ R) :
    A.det.natAbs ≤ R ^ n := by
  have hle := natAbs_det_le_prod_rowSum n A
  have hprod : (∏ i : Fin n, ∑ j, (A i j).natAbs) ≤ ∏ _i : Fin n, R := by
    gcongr with i
    exact h i
  have hpow : (∏ _i : Fin n, R) = R ^ n := by
    simp [prod_const, card_univ, Fintype.card_fin]
  exact hle.trans (hprod.trans_eq hpow)

end Span
