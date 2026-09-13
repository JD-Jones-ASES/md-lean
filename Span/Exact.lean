import Span.Basic

namespace Span

open Scheme

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

lemma not_edge_of_three_verts {s : Scheme} (h : 3 ≤ verts s) : s ≠ .edge := by
  rintro rfl
  simp [verts] at h

lemma verts_eq_two_iff (s : Scheme) : verts s = 2 ↔ s = .edge := by
  constructor
  · intro h
    cases s with
    | edge => rfl
    | cycle k =>
        simp [verts] at h
        try omega
    | series A B =>
        have hA := two_le_verts A
        have hB := two_le_verts B
        simp [verts] at h
        omega
    | join H K =>
        have hH := two_le_verts H
        have hK := two_le_verts K
        simp [verts] at h
        omega
  · rintro rfl
    rfl

lemma span_eq_one_iff (s : Scheme) : span s = 1 ↔ s = .edge := by
  constructor
  · intro h
    cases s with
    | edge => rfl
    | cycle k =>
        simp [span] at h
        try omega
    | series A B =>
        have hA := one_le_span A
        have hB := one_le_span B
        simp [span] at h
        omega
    | join H K =>
        have hH := one_le_span H
        simp [span] at h
        split_ifs at h <;> omega
  · rintro rfl
    rfl

lemma sub_one_le_of_le_succ {x y : ℕ} (hx : 1 ≤ x) (h : x ≤ y + 1) :
    x - 1 ≤ y := by omega

lemma sub_three_le_of_le_add_three {x y : ℕ} (hx : 3 ≤ x) (h : x ≤ y + 3) :
    x - 3 ≤ y := by omega

/-- Weak vertex budget, and a stronger one on every non-edge. These must
    be proved together: a nontrivial join is one vertex short of the weak
    bound if the children only supply the weak estimate. -/
lemma verts_budget : ∀ s : Scheme, WellFormed s →
    2 * joinCount s + 2 ≤ verts s ∧
    (s ≠ .edge → 2 * joinCount s + 3 ≤ verts s)
  | .edge, _ => by
      constructor
      · simp [joinCount, verts]
      · intro h
        exact (h rfl).elim
  | .cycle k, _ => by
      simp [joinCount, verts]
      try omega
  | .series A B, h => by
      have ⟨hAw, _⟩ := verts_budget A h.1
      have ⟨hBw, _⟩ := verts_budget B h.2
      simp [joinCount, verts]
      omega
  | .join H K, h => by
      have ⟨hHw, hHs⟩ := verts_budget H h.1
      have ⟨hKw, hKs⟩ := verts_budget K h.2.1
      refine ⟨?weak, fun _ => ?strong⟩
      · unfold joinCount verts
        split_ifs with hgt
        · have hHK := h.2.2.2 hgt
          have nH := hHs (not_edge_of_three_verts hHK.1)
          have nK := hKs (not_edge_of_three_verts hHK.2)
          omega
        · have hK1 : span K = 1 := by
            have := one_le_span K
            omega
          have hvK : verts K = 2 := h.2.2.1 hK1
          have hjK : joinCount K = 0 := by
            have hKe : K = .edge := (verts_eq_two_iff K).mp hvK
            simp [hKe, joinCount]
          omega
      · unfold joinCount verts
        split_ifs with hgt
        · have hHK := h.2.2.2 hgt
          have nH := hHs (not_edge_of_three_verts hHK.1)
          have nK := hKs (not_edge_of_three_verts hHK.2)
          omega
        · have hK1 : span K = 1 := by
            have := one_le_span K
            omega
          have hvK : verts K = 2 := h.2.2.1 hK1
          have hjK : joinCount K = 0 := by
            have hKe : K = .edge := (verts_eq_two_iff K).mp hvK
            simp [hKe, joinCount]
          omega

lemma series_slack {α β r s : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    α * r + β * s ≤ α * β * (r + s - 1) + 1 := by
  have hrs : 1 ≤ r + s := by omega
  have hα' : (1 : ℤ) ≤ (α : ℤ) := Nat.cast_le.mpr hα
  have hβ' : (1 : ℤ) ≤ (β : ℤ) := Nat.cast_le.mpr hβ
  have hr' : (2 : ℤ) ≤ (r : ℤ) := Nat.cast_le.mpr hr
  have hs' : (2 : ℤ) ≤ (s : ℤ) := Nat.cast_le.mpr hs
  have hrs' : ((r + s - 1 : ℕ) : ℤ) = (r : ℤ) + s - 1 := by
    simp [Nat.cast_sub hrs, Nat.cast_add]
  have h : ((α * r + β * s : ℕ) : ℤ) ≤
      ((α * β * (r + s - 1) + 1 : ℕ) : ℤ) := by
    push_cast
    rw [hrs']
    have diff :
        (α : ℤ) * β * (r + s - 1) + 1 - (α * r + β * s) =
          α * (β - 1) * (r - 1) + β * (α - 1) * (s - 1) +
            (α - 1) * (β - 1) := by
      ring
    have ha : (0 : ℤ) ≤ α := Int.natCast_nonneg _
    have hb : (0 : ℤ) ≤ β := Int.natCast_nonneg _
    have ha1 : (0 : ℤ) ≤ α - 1 := sub_nonneg.mpr hα'
    have hb1 : (0 : ℤ) ≤ β - 1 := sub_nonneg.mpr hβ'
    have hr1 : (0 : ℤ) ≤ r - 1 := sub_nonneg.mpr (le_trans (by decide) hr')
    have hs1 : (0 : ℤ) ≤ s - 1 := sub_nonneg.mpr (le_trans (by decide) hs')
    have h1 : (0 : ℤ) ≤ α * (β - 1) * (r - 1) :=
      mul_nonneg (mul_nonneg ha hb1) hr1
    have h2 : (0 : ℤ) ≤ β * (α - 1) * (s - 1) :=
      mul_nonneg (mul_nonneg hb ha1) hs1
    have h3 : (0 : ℤ) ≤ (α - 1) * (β - 1) := mul_nonneg ha1 hb1
    linarith
  exact Nat.cast_le.mp h

lemma join_slack {α β r s : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hr : 3 ≤ r) (hs : 3 ≤ s) :
    2 * α * r + β * s ≤ 2 * α * β * (r + s - 3) + 3 := by
  have hrs : 3 ≤ r + s := by omega
  have hα' : (1 : ℤ) ≤ (α : ℤ) := Nat.cast_le.mpr hα
  have hβ' : (1 : ℤ) ≤ (β : ℤ) := Nat.cast_le.mpr hβ
  have hr' : (3 : ℤ) ≤ (r : ℤ) := Nat.cast_le.mpr hr
  have hs' : (3 : ℤ) ≤ (s : ℤ) := Nat.cast_le.mpr hs
  have hrs' : ((r + s - 3 : ℕ) : ℤ) = (r : ℤ) + s - 3 := by
    simp [Nat.cast_sub hrs, Nat.cast_add]
  have h : ((2 * α * r + β * s : ℕ) : ℤ) ≤
      ((2 * α * β * (r + s - 3) + 3 : ℕ) : ℤ) := by
    push_cast
    rw [hrs']
    have diff :
        (2 : ℤ) * α * β * (r + s - 3) + 3 - (2 * α * r + β * s) =
          2 * α * (β - 1) * (r - 3) + β * (2 * α - 1) * (s - 3) +
            3 * (β - 1) * (2 * α - 1) := by
      ring
    have ha : (0 : ℤ) ≤ α := Int.natCast_nonneg _
    have hb : (0 : ℤ) ≤ β := Int.natCast_nonneg _
    have ha1 : (0 : ℤ) ≤ α - 1 := sub_nonneg.mpr hα'
    have hb1 : (0 : ℤ) ≤ β - 1 := sub_nonneg.mpr hβ'
    have hr3 : (0 : ℤ) ≤ r - 3 := sub_nonneg.mpr hr'
    have hs3 : (0 : ℤ) ≤ s - 3 := sub_nonneg.mpr hs'
    have h2a : (0 : ℤ) ≤ 2 * α - 1 := by
      have : (2 : ℤ) ≤ 2 * α := by nlinarith
      linarith
    have h1 : (0 : ℤ) ≤ 2 * α * (β - 1) * (r - 3) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by decide) ha) hb1) hr3
    have h2 : (0 : ℤ) ≤ β * (2 * α - 1) * (s - 3) :=
      mul_nonneg (mul_nonneg hb h2a) hs3
    have h3 : (0 : ℤ) ≤ 3 * (β - 1) * (2 * α - 1) :=
      mul_nonneg (mul_nonneg (by decide) hb1) h2a
    linarith
  exact Nat.cast_le.mp h

lemma join_span_of_trivial {H K : Scheme} (h : span K = 1) :
    span (.join H K) = span H + 1 := by
  have hW : span K - 1 = 0 := by omega
  simp [span, hW]

lemma join_span_of_nontrivial {H K : Scheme} (h : 1 < span K) :
    span (.join H K) =
      span H + span K + max (span H) (span K) - 1 := by
  have hH := one_le_span H
  have hK := one_le_span K
  have hW : span K - 1 ≠ 0 := by omega
  simp [span, hW]
  cases le_total (span H - 1) (span K - 1) with
  | inl hle =>
      rw [max_eq_right hle, max_eq_right (by omega : span H ≤ span K)]
      omega
  | inr hle =>
      rw [max_eq_left hle, max_eq_left (by omega : span K ≤ span H)]
      omega

lemma pow_two_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, pow_add]
  exact Nat.le_mul_of_pos_right (2 ^ a) (one_le_pow_two k)

lemma two_le_two_pow {t : ℕ} (ht : 1 ≤ t) : 2 ≤ 2 ^ t := by
  calc
    2 = 2 ^ 1 := by simp [pow_one]
    _ ≤ 2 ^ t := pow_two_mono ht

lemma two_mul_le_two_pow {t : ℕ} (ht : 1 ≤ t) : 2 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base =>
      simp [pow_one]
  | succ t ht ih =>
      calc
        2 * (t + 1) = 2 * t + 2 := by omega
        _ ≤ 2 ^ t + 2 ^ t := Nat.add_le_add ih (two_le_two_pow ht)
        _ = 2 ^ (t + 1) := two_pow_add_self t

lemma odd_margin_bound (t : ℕ) : 3 + 2 * t ≤ 3 * 2 ^ t := by
  induction t with
  | zero =>
      simp [pow_zero]
  | succ t ih =>
      have h2 : 2 ≤ 3 * 2 ^ t := by
        have := one_le_pow_two t
        omega
      calc
        3 + 2 * (t + 1) = 3 + 2 * t + 2 := by omega
        _ ≤ 3 * 2 ^ t + 3 * 2 ^ t := Nat.add_le_add ih h2
        _ = 3 * (2 ^ t + 2 ^ t) := by ring
        _ = 3 * 2 ^ (t + 1) := by rw [two_pow_add_self]

lemma exactCap_add_one {n : ℕ} (_hn : 2 ≤ n) :
    exactCap n + 1 =
      if n % 2 = 0 then 2 ^ (n / 2) else 3 * 2 ^ ((n - 3) / 2) := by
  unfold exactCap
  split_ifs with h
  · have : 1 ≤ 2 ^ (n / 2) := one_le_pow_two _
    omega
  · have : 1 ≤ 3 * 2 ^ ((n - 3) / 2) := by
      have := one_le_pow_two ((n - 3) / 2)
      omega
    omega

/-- `2^j (n - 2j)` is at most `F(n)+1` on the weak vertex budget. -/
lemma potential_le_exactCap {n j : ℕ} (hn : 2 ≤ n) (hj : 2 * j + 2 ≤ n) :
    2 ^ j * (n - 2 * j) ≤ exactCap n + 1 := by
  rw [exactCap_add_one hn]
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [if_pos h0]
    have ht : 1 ≤ n / 2 - j := by omega
    have hsum : j + (n / 2 - j) = n / 2 := by omega
    have hmargin : n - 2 * j = 2 * (n / 2 - j) := by omega
    have hpow : 2 ^ (n / 2) = 2 ^ j * 2 ^ (n / 2 - j) := by
      rw [← pow_add, hsum]
    rw [hmargin, hpow]
    exact Nat.mul_le_mul_left (2 ^ j) (two_mul_le_two_pow ht)
  · rw [if_neg (by omega : ¬ n % 2 = 0)]
    have hj' : j ≤ (n - 3) / 2 := by omega
    have hmargin : n - 2 * j = 3 + 2 * ((n - 3) / 2 - j) := by omega
    have hsum : j + ((n - 3) / 2 - j) = (n - 3) / 2 := by omega
    have hpow : 2 ^ ((n - 3) / 2) = 2 ^ j * 2 ^ ((n - 3) / 2 - j) := by
      rw [← pow_add, hsum]
    rw [hmargin, hpow]
    set t := (n - 3) / 2 - j
    have hodd := odd_margin_bound t
    have hcomm : 3 * (2 ^ j * 2 ^ t) = 2 ^ j * (3 * 2 ^ t) := by ring
    rw [hcomm]
    exact Nat.mul_le_mul_left (2 ^ j) hodd

lemma series_budget {A B : Scheme}
    (hAw : 2 * joinCount A + 2 ≤ verts A)
    (hBw : 2 * joinCount B + 2 ≤ verts B)
    (ihA : span A + 1 ≤ 2 ^ joinCount A * (verts A - 2 * joinCount A))
    (ihB : span B + 1 ≤ 2 ^ joinCount B * (verts B - 2 * joinCount B)) :
    span A + span B + 1 ≤
      2 ^ (joinCount A + joinCount B) *
        (verts A + verts B - 1 - 2 * (joinCount A + joinCount B)) := by
  set α := 2 ^ joinCount A
  set β := 2 ^ joinCount B
  set r := verts A - 2 * joinCount A
  set s := verts B - 2 * joinCount B
  have hα : 1 ≤ α := one_le_pow_two _
  have hβ : 1 ≤ β := one_le_pow_two _
  have hr : 2 ≤ r := by omega
  have hs : 2 ≤ s := by omega
  have hslack := series_slack (α := α) (β := β) (r := r) (s := s) hα hβ hr hs
  have hpow : 2 ^ (joinCount A + joinCount B) = α * β := pow_add _ _ _
  have hmargin : r + s - 1 =
      verts A + verts B - 1 - 2 * (joinCount A + joinCount B) := by
    omega
  have hsum : (span A + 1) + (span B + 1) ≤ α * r + β * s :=
    Nat.add_le_add ihA ihB
  have hx : 1 ≤ (span A + 1) + (span B + 1) := by omega
  have hleft : span A + span B + 1 = (span A + 1) + (span B + 1) - 1 := by
    omega
  have h1 : (span A + 1) + (span B + 1) - 1 ≤ α * r + β * s - 1 :=
    Nat.sub_le_sub_right hsum 1
  have hy : 1 ≤ α * r + β * s := by
    have : 1 ≤ α * r := Nat.mul_le_mul hα (by omega : 1 ≤ r)
    omega
  have h2 : α * r + β * s - 1 ≤ α * β * (r + s - 1) :=
    sub_one_le_of_le_succ hy hslack
  calc
    span A + span B + 1 = (span A + 1) + (span B + 1) - 1 := hleft
    _ ≤ α * r + β * s - 1 := h1
    _ ≤ α * β * (r + s - 1) := h2
    _ = 2 ^ (joinCount A + joinCount B) *
          (verts A + verts B - 1 - 2 * (joinCount A + joinCount B)) := by
        rw [hpow, hmargin]

lemma join_budget_nontrivial {H K : Scheme}
    (hgt : 1 < span K)
    (nH : 2 * joinCount H + 3 ≤ verts H)
    (nK : 2 * joinCount K + 3 ≤ verts K)
    (ihH : span H + 1 ≤ 2 ^ joinCount H * (verts H - 2 * joinCount H))
    (ihK : span K + 1 ≤ 2 ^ joinCount K * (verts K - 2 * joinCount K)) :
    span (.join H K) + 1 ≤
      2 ^ (joinCount H + joinCount K + 1) *
        (verts H + verts K - 1 - 2 * (joinCount H + joinCount K + 1)) := by
  set α := 2 ^ joinCount H
  set β := 2 ^ joinCount K
  set r := verts H - 2 * joinCount H
  set s := verts K - 2 * joinCount K
  have hα : 1 ≤ α := one_le_pow_two _
  have hβ : 1 ≤ β := one_le_pow_two _
  have hr : 3 ≤ r := by omega
  have hs : 3 ≤ s := by omega
  have sH := one_le_span H
  have sK := one_le_span K
  have hsp := join_span_of_nontrivial (H := H) hgt
  have hpow : 2 ^ (joinCount H + joinCount K + 1) = 2 * α * β := by
    rw [pow_add, pow_add, pow_one]
    ring
  have hmargin : r + s - 3 =
      verts H + verts K - 1 - 2 * (joinCount H + joinCount K + 1) := by
    omega
  cases le_total (span H) (span K) with
  | inl hle =>
      have hS : span (.join H K) + 1 = (span H + 1) + 2 * (span K + 1) - 3 := by
        rw [hsp, max_eq_right hle]
        omega
      have hsum : (span H + 1) + 2 * (span K + 1) ≤ α * r + 2 * (β * s) := by
        have := Nat.mul_le_mul_left 2 ihK
        omega
      have hx : 3 ≤ (span H + 1) + 2 * (span K + 1) := by omega
      have h1 : (span H + 1) + 2 * (span K + 1) - 3 ≤ α * r + 2 * (β * s) - 3 :=
        Nat.sub_le_sub_right hsum 3
      have hslack := join_slack (α := β) (β := α) (r := s) (s := r) hβ hα hs hr
      have hy : 3 ≤ α * r + 2 * (β * s) := by
        have : 1 ≤ β * s := Nat.mul_le_mul hβ (by omega : 1 ≤ s)
        omega
      have h2 : α * r + 2 * (β * s) - 3 ≤ 2 * β * α * (s + r - 3) := by
        have hslack' : 2 * β * s + α * r ≤ 2 * β * α * (s + r - 3) + 3 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hslack
        have hrew : α * r + 2 * (β * s) = 2 * β * s + α * r := by ring
        rw [hrew]
        exact sub_three_le_of_le_add_three (by omega) hslack'
      have hcomm : s + r - 3 = r + s - 3 := by omega
      calc
        span (.join H K) + 1
            = (span H + 1) + 2 * (span K + 1) - 3 := hS
        _ ≤ α * r + 2 * (β * s) - 3 := h1
        _ ≤ 2 * β * α * (s + r - 3) := h2
        _ = 2 * α * β * (r + s - 3) := by rw [hcomm]; ring
        _ = 2 ^ (joinCount H + joinCount K + 1) *
              (verts H + verts K - 1 -
                2 * (joinCount H + joinCount K + 1)) := by
            rw [hpow, hmargin]
  | inr hle =>
      have hS : span (.join H K) + 1 = 2 * (span H + 1) + (span K + 1) - 3 := by
        rw [hsp, max_eq_left hle]
        omega
      have hsum : 2 * (span H + 1) + (span K + 1) ≤ 2 * (α * r) + β * s := by
        have := Nat.mul_le_mul_left 2 ihH
        omega
      have hx : 3 ≤ 2 * (span H + 1) + (span K + 1) := by omega
      have h1 : 2 * (span H + 1) + (span K + 1) - 3 ≤ 2 * (α * r) + β * s - 3 :=
        Nat.sub_le_sub_right hsum 3
      have hslack := join_slack (α := α) (β := β) (r := r) (s := s) hα hβ hr hs
      have hy : 3 ≤ 2 * (α * r) + β * s := by
        have : 1 ≤ α * r := Nat.mul_le_mul hα (by omega : 1 ≤ r)
        omega
      have h2 : 2 * (α * r) + β * s - 3 ≤ 2 * α * β * (r + s - 3) := by
        have hslack' : 2 * (α * r) + β * s ≤ 2 * α * β * (r + s - 3) + 3 := by
          simpa [mul_assoc] using hslack
        exact sub_three_le_of_le_add_three hy hslack'
      calc
        span (.join H K) + 1
            = 2 * (span H + 1) + (span K + 1) - 3 := hS
        _ ≤ 2 * (α * r) + β * s - 3 := h1
        _ ≤ 2 * α * β * (r + s - 3) := h2
        _ = 2 ^ (joinCount H + joinCount K + 1) *
              (verts H + verts K - 1 -
                2 * (joinCount H + joinCount K + 1)) := by
            rw [hpow, hmargin]

lemma join_budget_trivial {H K : Scheme}
    (hK1 : span K = 1) (hvK : verts K = 2)
    (hHw : 2 * joinCount H + 2 ≤ verts H)
    (ihH : span H + 1 ≤ 2 ^ joinCount H * (verts H - 2 * joinCount H)) :
    span (.join H K) + 1 ≤
      2 ^ joinCount H * (verts H + verts K - 1 - 2 * joinCount H) := by
  have htr := join_span_of_trivial (H := H) hK1
  have hα : 1 ≤ 2 ^ joinCount H := one_le_pow_two _
  have hS : span (.join H K) + 1 = span H + 1 + 1 := by rw [htr]
  have hrew : verts H + verts K - 1 - 2 * joinCount H =
      (verts H - 2 * joinCount H) + 1 := by omega
  have hadd : span H + 1 + 1 ≤
      2 ^ joinCount H * (verts H - 2 * joinCount H) + 1 :=
    Nat.add_le_add_right ihH 1
  have hmul : 2 ^ joinCount H * (verts H - 2 * joinCount H) + 1 ≤
      2 ^ joinCount H * ((verts H - 2 * joinCount H) + 1) := by
    have : 2 ^ joinCount H * (verts H - 2 * joinCount H) + 2 ^ joinCount H =
        2 ^ joinCount H * ((verts H - 2 * joinCount H) + 1) := by
      ring
    omega
  rw [hS, hrew]
  exact hadd.trans hmul

/-- Two-parameter exact budget: `S = T+1 ≤ 2^j (n-2j)`. -/
theorem span_succ_le_join_budget : ∀ s : Scheme, WellFormed s →
    span s + 1 ≤ 2 ^ joinCount s * (verts s - 2 * joinCount s)
  | .edge, _ => by
      simp [span, joinCount, verts]
  | .cycle k, _ => by
      simp [span, joinCount, verts]
  | .series A B, h => by
      have ihA := span_succ_le_join_budget A h.1
      have ihB := span_succ_le_join_budget B h.2
      have ⟨hAw, _⟩ := verts_budget A h.1
      have ⟨hBw, _⟩ := verts_budget B h.2
      simpa [span, verts, joinCount] using series_budget hAw hBw ihA ihB
  | .join H K, h => by
      have ihH := span_succ_le_join_budget H h.1
      have ihK := span_succ_le_join_budget K h.2.1
      have ⟨hHw, hHs⟩ := verts_budget H h.1
      have ⟨hKw, hKs⟩ := verts_budget K h.2.1
      by_cases hgt : 1 < span K
      · have hHK := h.2.2.2 hgt
        have nH := hHs (not_edge_of_three_verts hHK.1)
        have nK := hKs (not_edge_of_three_verts hHK.2)
        have hmain := join_budget_nontrivial hgt nH nK ihH ihK
        simpa [joinCount, verts, if_pos hgt] using hmain
      · have hK1 : span K = 1 := by
          have := one_le_span K
          omega
        have hvK : verts K = 2 := h.2.2.1 hK1
        have hKe : K = .edge := (verts_eq_two_iff K).mp hvK
        have hjK : joinCount K = 0 := by simp [hKe, joinCount]
        have hmain := join_budget_trivial hK1 hvK hHw ihH
        simp [joinCount, verts, hjK, hvK, if_neg hgt] at hmain ⊢
        exact hmain

theorem span_le_exact (s : Scheme) (h : WellFormed s) :
    span s ≤ exactCap (verts s) := by
  have hbudget := span_succ_le_join_budget s h
  have ⟨hw, _⟩ := verts_budget s h
  have hpot := potential_le_exactCap (two_le_verts s) hw
  have : span s + 1 ≤ exactCap (verts s) + 1 := hbudget.trans hpot
  omega

/-- A 3-cycle, used as the triangle attached at each nontrivial join. -/
def triangle : Scheme := .cycle 0

lemma triangle_verts : verts triangle = 3 := rfl
lemma triangle_span : span triangle = 2 := rfl
lemma triangle_joinCount : joinCount triangle = 0 := rfl
lemma triangle_wf : WellFormed triangle := trivial
lemma triangle_span_gt : 1 < span triangle := by
  change 1 < 2
  omega

def attachTriangles : Scheme → ℕ → Scheme
  | base, 0 => base
  | base, j + 1 => .join (attachTriangles base j) triangle

lemma attachTriangles_verts (base : Scheme) :
    ∀ j, verts (attachTriangles base j) = verts base + 2 * j
  | 0 => rfl
  | j + 1 => by
      simp [attachTriangles, verts, triangle_verts, attachTriangles_verts base j]
      omega

lemma attachTriangles_joinCount (base : Scheme) :
    ∀ j, joinCount (attachTriangles base j) = joinCount base + j
  | 0 => rfl
  | j + 1 => by
      have ih := attachTriangles_joinCount base j
      simp [attachTriangles, joinCount, triangle_span, triangle_joinCount, ih]
      omega

lemma attachTriangles_span (base : Scheme) (hbase : 2 ≤ span base) :
    ∀ j, span (attachTriangles base j) = 2 ^ j * (span base + 1) - 1
  | 0 => by
      change span base = 2 ^ 0 * (span base + 1) - 1
      simp [pow_zero]
      try omega
  | j + 1 => by
      have ih := attachTriangles_span base hbase j
      have hsp := join_span_of_nontrivial (H := attachTriangles base j)
        triangle_span_gt
      have hx : 1 ≤ 2 ^ j * (span base + 1) :=
        (one_le_pow_two j).trans
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      have hH : 2 ≤ span (attachTriangles base j) := by
        rw [ih]
        have hp : 1 ≤ 2 ^ j := one_le_pow_two j
        have hq : 3 ≤ span base + 1 := Nat.succ_le_succ hbase
        have hmul : 3 ≤ 2 ^ j * (span base + 1) := by
          have := Nat.mul_le_mul hp hq
          simpa using this
        exact Nat.le_sub_of_add_le (by omega)
      have hmax :
          max (span (attachTriangles base j)) (span triangle) =
            span (attachTriangles base j) :=
        max_eq_left (by simpa [triangle_span] using hH)
      have hjoin : span (.join (attachTriangles base j) triangle) =
          2 * span (attachTriangles base j) + 1 := by
        rw [hsp, hmax]
        simp [triangle_span]
        have := one_le_span (attachTriangles base j)
        omega
      simp only [attachTriangles]
      rw [hjoin, ih]
      have hsub : 2 * (2 ^ j * (span base + 1) - 1) + 1 =
          2 * (2 ^ j * (span base + 1)) - 1 := by omega
      rw [hsub]
      suffices 2 * (2 ^ j * (span base + 1)) =
          2 ^ (j + 1) * (span base + 1) by
        omega
      rw [pow_succ]
      ring

lemma attachTriangles_wf (base : Scheme) (hwf : WellFormed base)
    (hv : 3 ≤ verts base) :
    ∀ j, WellFormed (attachTriangles base j)
  | 0 => hwf
  | j + 1 => by
      refine ⟨attachTriangles_wf base hwf hv j, triangle_wf, ?_, ?_⟩
      · intro hsp
        simp [triangle_span] at hsp
      · intro _
        refine ⟨?_, by simp [triangle_verts]⟩
        have := attachTriangles_verts base j
        omega

lemma exactCap_eq_max_join {n : ℕ} (hn : 3 ≤ n) :
    2 ^ ((n - 3) / 2) * (n - 2 * ((n - 3) / 2)) - 1 = exactCap n := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · unfold exactCap
    rw [if_pos h0]
    have hmargin : n - 2 * ((n - 3) / 2) = 4 := by omega
    have hj : (n - 3) / 2 = n / 2 - 2 := by omega
    rw [hmargin, hj]
    have ht : 2 ≤ n / 2 := by omega
    have hpow : 2 ^ (n / 2 - 2) * 4 = 2 ^ (n / 2) := by
      calc
        2 ^ (n / 2 - 2) * 4 = 2 ^ (n / 2 - 2) * 2 ^ 2 := by norm_num
        _ = 2 ^ (n / 2 - 2 + 2) := (pow_add _ _ _).symm
        _ = 2 ^ (n / 2) := by
            congr 1
            omega
    omega
  · unfold exactCap
    rw [if_neg (by omega : ¬ n % 2 = 0)]
    have hmargin : n - 2 * ((n - 3) / 2) = 3 := by omega
    rw [hmargin]
    omega

theorem exists_span_eq_join_budget (n j : ℕ)
    (h : n = 2 ∧ j = 0 ∨ 2 * j + 3 ≤ n) :
    ∃ s : Scheme, WellFormed s ∧ verts s = n ∧ joinCount s = j ∧
      span s + 1 = 2 ^ j * (n - 2 * j) := by
  rcases h with ⟨hn, hj⟩ | hadm
  · subst hn
    subst hj
    refine ⟨.edge, trivial, rfl, rfl, ?_⟩
    simp [span]
  · set m := n - 2 * j
    have hm : 3 ≤ m := by omega
    set base : Scheme := .cycle (m - 3)
    have hv : verts base = m := by simp [verts, base]; omega
    have hs : span base = m - 1 := by simp [span, base]; omega
    have hj0 : joinCount base = 0 := rfl
    have hwf : WellFormed base := trivial
    have h3 : 3 ≤ verts base := by omega
    have hspan2 : 2 ≤ span base := by omega
    refine ⟨attachTriangles base j,
      attachTriangles_wf base hwf h3 j, ?_, ?_, ?_⟩
    · rw [attachTriangles_verts, hv]; omega
    · rw [attachTriangles_joinCount, hj0, Nat.zero_add]
    · have hsp := attachTriangles_span base hspan2 j
      have hpos : 1 ≤ 2 ^ j * (span base + 1) :=
        (one_le_pow_two j).trans
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      have hclear : span (attachTriangles base j) + 1 =
          2 ^ j * (span base + 1) := by
        rw [hsp]
        omega
      rw [hclear, hs]
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1]

theorem exists_span_eq_exact (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Scheme, WellFormed s ∧ verts s = n ∧ span s = exactCap n := by
  rcases Nat.eq_or_lt_of_le hn with h2 | h3
  · cases h2
    refine ⟨.edge, trivial, rfl, ?_⟩
    simp [span, exactCap]
  · have hn3 : 3 ≤ n := by omega
    set j := (n - 3) / 2
    have hadm : 2 * j + 3 ≤ n := by omega
    obtain ⟨s, hwf, hv, _, hs⟩ :=
      exists_span_eq_join_budget n j (Or.inr hadm)
    refine ⟨s, hwf, hv, ?_⟩
    have hcap := exactCap_eq_max_join hn3
    have hspan : span s = 2 ^ j * (n - 2 * j) - 1 := by omega
    calc
      span s = 2 ^ j * (n - 2 * j) - 1 := hspan
      _ = exactCap n := hcap

end Span
