import Mathlib
import Span.Det

namespace Span

open Finset

variable {n : ℕ}

/-- Upward neighbour sum \(P_s = \sum_{t\sim s}\max\{h(t)-h(s),0\}\). -/
def upwardSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then h t - h s else 0

/-- Downward neighbour sum \(N_s = \sum_{t\sim s}\max\{h(s)-h(t),0\}\). -/
def downwardSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then h s - h t else 0

lemma term_le_T {T : ℕ} {Adj : Fin n → Fin n → Bool} {h : Fin n → ℕ}
    (hh : ∀ i, h i ≤ T) (s t : Fin n) :
    (if Adj s t then h t - h s else 0) ≤ T := by
  split_ifs
  · exact (Nat.sub_le _ _).trans (hh t)
  · exact Nat.zero_le _

lemma upwardSum_le {T : ℕ} (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (hh : ∀ i, h i ≤ T) (s : Fin n) :
    upwardSum Adj h s ≤ (n - 1) * T := by
  have hsplit := sum_erase_add (s := univ) (a := s)
    (f := fun t => if Adj s t then h t - h s else 0) (mem_univ s)
  have hs : (if Adj s s then h s - h s else 0) = 0 := by simp
  have hrest :
      ∑ t ∈ univ.erase s, (if Adj s t then h t - h s else 0) ≤
        ∑ _t ∈ univ.erase s, T := by
    gcongr with t ht
    exact term_le_T hh s t
  have hcard : ∑ _t ∈ univ.erase s, T = (n - 1) * T := by
    simp [card_erase_of_mem (mem_univ s), card_univ, Fintype.card_fin, smul_eq_mul]
  have : upwardSum Adj h s =
      (if Adj s s then h s - h s else 0) +
        ∑ t ∈ univ.erase s, (if Adj s t then h t - h s else 0) := by
    simpa [upwardSum] using hsplit.symm
  calc
    upwardSum Adj h s = 0 + ∑ t ∈ univ.erase s, (if Adj s t then h t - h s else 0) := by
      simpa [hs] using this
    _ ≤ (n - 1) * T := by
        simpa [hcard] using hrest

lemma downwardSum_le {T : ℕ} (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (hh : ∀ i, h i ≤ T) (s : Fin n) :
    downwardSum Adj h s ≤ (n - 1) * T := by
  -- same argument with heights reversed through T - h
  have hsplit := sum_erase_add (s := univ) (a := s)
    (f := fun t => if Adj s t then h s - h t else 0) (mem_univ s)
  have hs : (if Adj s s then h s - h s else 0) = 0 := by simp
  have hrest :
      ∑ t ∈ univ.erase s, (if Adj s t then h s - h t else 0) ≤
        ∑ _t ∈ univ.erase s, T := by
    gcongr with t ht
    split_ifs
    · exact (Nat.sub_le _ _).trans (hh s)
    · exact Nat.zero_le _
  have hcard : ∑ _t ∈ univ.erase s, T = (n - 1) * T := by
    simp [card_erase_of_mem (mem_univ s), card_univ, Fintype.card_fin, smul_eq_mul]
  have : downwardSum Adj h s =
      (if Adj s s then h s - h s else 0) +
        ∑ t ∈ univ.erase s, (if Adj s t then h s - h t else 0) := by
    simpa [downwardSum] using hsplit.symm
  calc
    downwardSum Adj h s = 0 + ∑ t ∈ univ.erase s, (if Adj s t then h s - h t else 0) := by
      simpa [hs] using this
    _ ≤ (n - 1) * T := by
        simpa [hcard] using hrest

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

lemma dartWeight_interior_le {T : ℕ} (Adj : Fin n → Fin n → Bool)
    (h : Fin n → ℕ) (B : Finset (Fin n)) (hh : ∀ i, h i ≤ T)
    {s : Fin n} (hs : s ∉ B) (t : Fin n) :
    dartWeight Adj h B s t ≤ (n - 1) * T := by
  unfold dartWeight
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact downwardSum_le Adj h hh s
  · exact upwardSum_le Adj h hh s
  · exact Nat.zero_le _

lemma dartWeight_self (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (s : Fin n) :
    dartWeight Adj h B s s = 0 := by
  simp [dartWeight]

lemma dartWeight_sum_le {T : ℕ} (Adj : Fin n → Fin n → Bool)
    (h : Fin n → ℕ) (B : Finset (Fin n)) (hh : ∀ i, h i ≤ T)
    {s : Fin n} (hs : s ∉ B) :
    ∑ t, dartWeight Adj h B s t ≤ (n - 1) ^ 2 * T := by
  have hsplit := sum_erase_add (s := univ) (a := s)
    (f := fun t => dartWeight Adj h B s t) (mem_univ s)
  have : ∑ t, dartWeight Adj h B s t =
      dartWeight Adj h B s s + ∑ t ∈ univ.erase s, dartWeight Adj h B s t := by
    rw [← hsplit, add_comm]
  have hrest :
      ∑ t ∈ univ.erase s, dartWeight Adj h B s t ≤
        ∑ _t ∈ univ.erase s, ((n - 1) * T) := by
    gcongr with t ht
    exact dartWeight_interior_le Adj h B hh hs t
  have hcard : ∑ _t ∈ univ.erase s, ((n - 1) * T) = (n - 1) * ((n - 1) * T) := by
    simp [card_erase_of_mem (mem_univ s), card_univ, Fintype.card_fin, smul_eq_mul]
  have hsq : (n - 1) * ((n - 1) * T) = (n - 1) ^ 2 * T := by
    rw [Nat.pow_two, mul_assoc]
  calc
    ∑ t, dartWeight Adj h B s t = ∑ t ∈ univ.erase s, dartWeight Adj h B s t := by
      simpa [dartWeight_self] using this
    _ ≤ (n - 1) ^ 2 * T := by
        simpa [hcard, hsq] using hrest

/-- Dirichlet matrix: unit rows on the boundary, weighted Laplacian
    on the interior, matching Mazur §3. -/
def dirichlet (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun s t =>
    if s ∈ B then (if s = t then 1 else 0)
    else if s = t then ∑ u : Fin n, (dartWeight Adj h B s u : ℤ)
    else - (dartWeight Adj h B s t : ℤ)

lemma dirichlet_boundary_rowSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) {s : Fin n} (hs : s ∈ B) :
    ∑ t, (dirichlet Adj h B s t).natAbs = 1 := by
  have habs : ∀ t, (dirichlet Adj h B s t).natAbs = if s = t then 1 else 0 := by
    intro t
    simp [dirichlet, hs]
    split_ifs <;> simp
  simp [habs]

lemma natAbs_sum_natCast (f : Fin n → ℕ) :
    (∑ t, (f t : ℤ)).natAbs = ∑ t, f t := by
  rw [← Nat.cast_sum, Int.natAbs_natCast]

lemma dirichlet_interior_rowSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) {s : Fin n} (hs : s ∉ B) :
    ∑ t, (dirichlet Adj h B s t).natAbs =
      2 * ∑ t, dartWeight Adj h B s t := by
  have hdiag : dirichlet Adj h B s s =
      ∑ u : Fin n, (dartWeight Adj h B s u : ℤ) := by
    simp [dirichlet, hs]
  have hoff : ∀ t, t ≠ s → dirichlet Adj h B s t = - (dartWeight Adj h B s t : ℤ) := by
    intro t ht
    have hne : s ≠ t := ht.symm
    simp [dirichlet, hs, hne]
  have hsplit := sum_erase_add (s := univ) (a := s)
    (f := fun t => (dirichlet Adj h B s t).natAbs) (mem_univ s)
  have hdiagAbs : (dirichlet Adj h B s s).natAbs = ∑ t, dartWeight Adj h B s t := by
    rw [hdiag, natAbs_sum_natCast]
  have hoffAbs : ∀ t ∈ univ.erase s, (dirichlet Adj h B s t).natAbs =
      dartWeight Adj h B s t := by
    intro t ht
    have htne : t ≠ s := ne_of_mem_erase ht
    rw [hoff t htne, Int.natAbs_neg, Int.natAbs_natCast]
  have : ∑ t, (dirichlet Adj h B s t).natAbs =
      (dirichlet Adj h B s s).natAbs +
        ∑ t ∈ univ.erase s, (dirichlet Adj h B s t).natAbs := by
    rw [← hsplit, add_comm]
  have hrest : ∑ t ∈ univ.erase s, (dirichlet Adj h B s t).natAbs =
      ∑ t ∈ univ.erase s, dartWeight Adj h B s t := by
    apply sum_congr rfl
    intro t ht
    exact hoffAbs t ht
  have hws : ∑ t, dartWeight Adj h B s t =
      ∑ t ∈ univ.erase s, dartWeight Adj h B s t := by
    have h2 := sum_erase_add (s := univ) (a := s)
      (f := fun t => dartWeight Adj h B s t) (mem_univ s)
    simpa [dartWeight_self, add_comm] using h2.symm
  calc
    ∑ t, (dirichlet Adj h B s t).natAbs =
        ∑ t, dartWeight Adj h B s t + ∑ t ∈ univ.erase s, dartWeight Adj h B s t := by
      simpa [hdiagAbs, hrest] using this
    _ = 2 * ∑ t, dartWeight Adj h B s t := by
        rw [← hws]
        ring

theorem dirichlet_rowSum_le {T : ℕ} (Adj : Fin n → Fin n → Bool)
    (h : Fin n → ℕ) (B : Finset (Fin n)) (hh : ∀ i, h i ≤ T)
    (hn : 2 ≤ n) (hT : 1 ≤ T) (s : Fin n) :
    ∑ t, (dirichlet Adj h B s t).natAbs ≤ 2 * (n - 1) ^ 2 * T := by
  by_cases hs : s ∈ B
  · have hbound := dirichlet_boundary_rowSum Adj h B hs
    have hnm : 1 ≤ n - 1 := by omega
    have hsq : 1 ≤ (n - 1) ^ 2 := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul hnm hnm
    have h1 : 1 ≤ (n - 1) ^ 2 * T := Nat.mul_le_mul hsq hT
    have h2 : (n - 1) ^ 2 * T ≤ 2 * (n - 1) ^ 2 * T := by
      have : (n - 1) ^ 2 * T ≤ 2 * ((n - 1) ^ 2 * T) :=
        Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
      simpa [mul_assoc] using this
    rw [hbound]
    exact h1.trans h2
  · have hrow := dirichlet_interior_rowSum Adj h B hs
    have hsum := dartWeight_sum_le Adj h B hh hs
    have hmul : 2 * ∑ t, dartWeight Adj h B s t ≤ 2 * ((n - 1) ^ 2 * T) :=
      Nat.mul_le_mul_left 2 hsum
    rw [hrow]
    convert hmul using 1
    ring

theorem dirichlet_det_le {T : ℕ} (Adj : Fin n → Fin n → Bool)
    (h : Fin n → ℕ) (B : Finset (Fin n)) (hh : ∀ i, h i ≤ T)
    (hn : 2 ≤ n) (hT : 1 ≤ T) :
    (dirichlet Adj h B).det.natAbs ≤ (2 * (n - 1) ^ 2 * T) ^ n :=
  natAbs_det_le_of_rowSum_le (dirichlet Adj h B)
    (fun s => dirichlet_rowSum_le Adj h B hh hn hT s)

end Span

