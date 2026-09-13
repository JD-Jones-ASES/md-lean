import Span.Weights

namespace Span

open Finset

variable {n : ℕ}

/-- Neighbours of `s` with strictly larger height. -/
def higherCount (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then (if h s < h t then 1 else 0) else 0

/-- Neighbours of `s` with strictly smaller height. -/
def lowerCount (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then (if h t < h s then 1 else 0) else 0

/-- Outgoing dart mass \(\delta_s=a_s N_s+b_s P_s\). -/
def dartMass (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  higherCount Adj h s * downwardSum Adj h s +
    lowerCount Adj h s * upwardSum Adj h s

private def higherFlag (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s t : Fin n) : ℕ :=
  if Adj s t then (if h s < h t then 1 else 0) else 0

private def lowerDiff (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s u : Fin n) : ℕ :=
  if Adj s u then (if h u < h s then h s - h u else 0) else 0

private def lowerFlag (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s u : Fin n) : ℕ :=
  if Adj s u then (if h u < h s then 1 else 0) else 0

private def higherDiff (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s t : Fin n) : ℕ :=
  if Adj s t then (if h s < h t then h t - h s else 0) else 0

lemma upwardSum_as_higher (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s : Fin n) :
    upwardSum Adj h s = ∑ t : Fin n, higherDiff Adj h s t := by
  apply sum_congr rfl
  intro t _
  unfold higherDiff
  split_ifs with hAdj hlt
  · rfl
  · have : h t ≤ h s := Nat.le_of_not_gt hlt
    simp [Nat.sub_eq_zero_of_le this]
  · rfl

lemma downwardSum_as_lower (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s : Fin n) :
    downwardSum Adj h s = ∑ t : Fin n, lowerDiff Adj h s t := by
  apply sum_congr rfl
  intro t _
  unfold lowerDiff
  split_ifs with hAdj hlt
  · rfl
  · have : h s ≤ h t := Nat.le_of_not_gt hlt
    simp [Nat.sub_eq_zero_of_le this]
  · rfl

lemma higherCount_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    higherCount Adj h s = ∑ t : Fin n, higherFlag Adj h s t := rfl

lemma lowerCount_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    lowerCount Adj h s = ∑ t : Fin n, lowerFlag Adj h s t := rfl

lemma pair_term_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s t u : Fin n) :
    higherFlag Adj h s t * lowerDiff Adj h s u +
        lowerFlag Adj h s u * higherDiff Adj h s t =
      if Adj s t then
        (if h s < h t then
          (if Adj s u then (if h u < h s then h t - h u else 0) else 0)
        else 0)
      else 0 := by
  unfold higherFlag lowerDiff lowerFlag higherDiff
  split_ifs <;> simp <;> omega

lemma dartMass_eq_pair_sum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (s : Fin n) :
    dartMass Adj h s =
      ∑ t : Fin n, ∑ u : Fin n,
        if Adj s t then
          (if h s < h t then
            (if Adj s u then (if h u < h s then h t - h u else 0) else 0)
          else 0)
        else 0 := by
  unfold dartMass
  rw [higherCount_eq, lowerCount_eq, upwardSum_as_higher, downwardSum_as_lower]
  have hAN :
      (∑ t, higherFlag Adj h s t) * (∑ u, lowerDiff Adj h s u) =
        ∑ t, ∑ u, higherFlag Adj h s t * lowerDiff Adj h s u :=
    sum_mul_sum univ univ _ _
  have hBP :
      (∑ u, lowerFlag Adj h s u) * (∑ t, higherDiff Adj h s t) =
        ∑ u, ∑ t, lowerFlag Adj h s u * higherDiff Adj h s t :=
    sum_mul_sum univ univ _ _
  have hBP' :
      (∑ u, lowerFlag Adj h s u) * (∑ t, higherDiff Adj h s t) =
        ∑ t, ∑ u, lowerFlag Adj h s u * higherDiff Adj h s t := by
    rw [hBP, sum_comm]
  rw [hAN, hBP']
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  exact pair_term_eq Adj h s t u

lemma pair_height_le_T {T : ℕ} {h : Fin n → ℕ} (hh : ∀ i, h i ≤ T)
    (s t u : Fin n) :
    (if h s < h t then (if h u < h s then h t - h u else 0) else 0) ≤ T := by
  split_ifs
  · exact (Nat.sub_le _ _).trans (hh t)
  · exact Nat.zero_le _
  · exact Nat.zero_le _

lemma lower_sum_T (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n)
    (T : ℕ) :
    (∑ u, if Adj s u then (if h u < h s then T else 0) else 0) =
      lowerCount Adj h s * T := by
  rw [lowerCount, sum_mul]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem dartMass_le {T : ℕ} (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (hh : ∀ i, h i ≤ T) (s : Fin n) :
    dartMass Adj h s ≤ higherCount Adj h s * lowerCount Adj h s * T := by
  have hpair := dartMass_eq_pair_sum Adj h s
  have hterm : ∀ t u : Fin n,
      (if Adj s t then
        (if h s < h t then
          (if Adj s u then (if h u < h s then h t - h u else 0) else 0)
        else 0)
      else 0) ≤
        higherFlag Adj h s t *
          (if Adj s u then (if h u < h s then T else 0) else 0) := by
    intro t u
    unfold higherFlag
    split_ifs <;> simp
    exact (hh t).trans (Nat.le_add_right _ _)
  have hbound :
      (∑ t, ∑ u,
          if Adj s t then
            (if h s < h t then
              (if Adj s u then (if h u < h s then h t - h u else 0) else 0)
            else 0)
          else 0) ≤
        ∑ t, ∑ u,
          higherFlag Adj h s t *
            (if Adj s u then (if h u < h s then T else 0) else 0) := by
    apply sum_le_sum
    intro t _
    apply sum_le_sum
    intro u _
    exact hterm t u
  have hfact :
      (∑ t, ∑ u,
          higherFlag Adj h s t *
            (if Adj s u then (if h u < h s then T else 0) else 0)) =
        higherCount Adj h s * lowerCount Adj h s * T := by
    have := sum_mul_sum univ univ
      (fun t => higherFlag Adj h s t)
      (fun u => if Adj s u then (if h u < h s then T else 0) else 0)
    rw [← this, higherCount_eq, lower_sum_T Adj h s T]
    ring
  have : dartMass Adj h s ≤ higherCount Adj h s * lowerCount Adj h s * T :=
    (hpair ▸ hbound).trans_eq hfact
  exact this

end Span
