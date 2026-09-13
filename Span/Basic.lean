import Mathlib

namespace Span

open Nat

inductive Scheme where
  | edge : Scheme
  | cycle (k : ℕ) : Scheme
  | series (A B : Scheme) : Scheme
  | join (H K : Scheme) : Scheme

open Scheme

def verts : Scheme → ℕ
  | edge => 2
  | cycle k => k + 3
  | series A B => verts A + verts B - 1
  | join H K => verts H + verts K - 1

def span : Scheme → ℕ
  | edge => 1
  | cycle k => k + 2
  | series A B => span A + span B
  | join H K =>
      let A := span H
      let W := span K - 1
      if W = 0 then A + 1 else A + 1 + max (A - 1) W + W

def WellFormed : Scheme → Prop
  | edge => True
  | cycle _ => True
  | series A B => WellFormed A ∧ WellFormed B
  | join H K =>
      WellFormed H ∧ WellFormed K ∧
      (span K = 1 → verts K = 2) ∧
      (1 < span K → 3 ≤ verts H ∧ 3 ≤ verts K)

lemma two_le_verts : ∀ s : Scheme, 2 ≤ verts s
  | .edge => by decide
  | .cycle k => by
      change 2 ≤ k + 3
      omega
  | .series A B => by
      have hA := two_le_verts A
      have hB := two_le_verts B
      change 2 ≤ verts A + verts B - 1
      omega
  | .join H K => by
      have hH := two_le_verts H
      have hK := two_le_verts K
      change 2 ≤ verts H + verts K - 1
      omega

lemma one_le_span : ∀ s : Scheme, 1 ≤ span s
  | .edge => by decide
  | .cycle k => by
      change 1 ≤ k + 2
      omega
  | .series A B => by
      have hA := one_le_span A
      have hB := one_le_span B
      change 1 ≤ span A + span B
      omega
  | .join H K => by
      have hH := one_le_span H
      simp [span]
      split_ifs <;> omega

lemma two_pow_add_self (n : ℕ) : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
  rw [← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]

lemma pow_two_paste {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 ^ (a - 1) + 2 ^ (b - 1) ≤ 2 ^ (a + b - 1) := by
  have h1 : a - 1 ≤ a + b - 2 := by omega
  have h2 : b - 1 ≤ a + b - 2 := by omega
  have hpow1 : 2 ^ (a - 1) ≤ 2 ^ (a + b - 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h1
  have hpow2 : 2 ^ (b - 1) ≤ 2 ^ (a + b - 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h2
  have hadd : 2 ^ (a + b - 2) + 2 ^ (a + b - 2) = 2 ^ (a + b - 1) := by
    have : a + b - 1 = (a + b - 2) + 1 := by omega
    rw [this, two_pow_add_self]
  exact (Nat.add_le_add hpow1 hpow2).trans_eq hadd

lemma join_span_le_double {A W : ℕ} (hA : 1 ≤ A) (hW : 1 ≤ W) :
    A + 1 + max (A - 1) W + W ≤ 2 * (A + W) := by
  cases le_total (A - 1) W with
  | inl h =>
      rw [Nat.max_eq_right h]
      omega
  | inr h =>
      rw [Nat.max_eq_left h]
      omega

lemma add_pred_le_mul {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    p + q - 1 ≤ p * q := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have : p' + q' + 1 ≤ p' * q' + p' + q' + 1 := by
      have : 0 ≤ p' * q' := Nat.zero_le _
      omega
    simpa [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using this

lemma cycle_bound (k : ℕ) : k + 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
      calc
        k + 1 + 2 = k + 3 := rfl
        _ ≤ 2 * (k + 2) := by omega
        _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ (k + 2) := (Nat.pow_succ 2 (k + 1)).symm

lemma one_le_pow_two (n : ℕ) : 1 ≤ 2 ^ n :=
  Nat.one_le_pow n 2 (by decide)

theorem span_le_two_pow : ∀ s : Scheme, WellFormed s →
    span s ≤ 2 ^ (verts s - 2)
  | .edge, _ => by decide
  | .cycle k, _ => by
      change k + 2 ≤ 2 ^ (k + 3 - 2)
      have : k + 3 - 2 = k + 1 := by omega
      rw [this]
      exact cycle_bound k
  | .series A B, h => by
      have ihA := span_le_two_pow A h.1
      have ihB := span_le_two_pow B h.2
      have vA := two_le_verts A
      have vB := two_le_verts B
      change span A + span B ≤ 2 ^ (verts A + verts B - 1 - 2)
      have ha : 1 ≤ verts A - 1 := by omega
      have hb : 1 ≤ verts B - 1 := by omega
      have hA' : span A ≤ 2 ^ ((verts A - 1) - 1) := by
        simpa [Nat.sub_sub] using ihA
      have hB' : span B ≤ 2 ^ ((verts B - 1) - 1) := by
        simpa [Nat.sub_sub] using ihB
      have hpaste := pow_two_paste ha hb
      have hsum : span A + span B ≤ 2 ^ (verts A - 1 + (verts B - 1) - 1) :=
        (Nat.add_le_add hA' hB').trans hpaste
      have hrew : verts A - 1 + (verts B - 1) - 1 = verts A + verts B - 1 - 2 := by
        omega
      simpa [hrew] using hsum
  | .join H K, h => by
      have ihH := span_le_two_pow H h.1
      have ihK := span_le_two_pow K h.2.1
      have vH := two_le_verts H
      have vK := two_le_verts K
      have sH := one_le_span H
      have sK := one_le_span K
      simp [span, verts]
      split_ifs with hW
      · have hK2 : verts K = 2 := by
          have : span K = 1 := by omega
          exact h.2.2.1 this
        have hpow : span H + 1 ≤ 2 ^ (verts H - 1) := by
          have hle : span H + 1 ≤ 2 ^ (verts H - 2) + 1 := Nat.add_le_add_right ihH 1
          have hpow' : 2 ^ (verts H - 2) + 1 ≤ 2 ^ (verts H - 1) := by
            have h1 : 1 ≤ 2 ^ (verts H - 2) := one_le_pow_two _
            have h2 : 2 ^ (verts H - 2) + 2 ^ (verts H - 2) = 2 ^ (verts H - 1) := by
              have : verts H - 1 = verts H - 2 + 1 := by omega
              rw [this, two_pow_add_self]
            omega
          exact hle.trans hpow'
        have hv : verts H + verts K - 1 - 2 = verts H - 1 := by omega
        simpa [hv] using hpow
      · have hWpos : 1 ≤ span K - 1 := by omega
        have hHK : 3 ≤ verts H ∧ 3 ≤ verts K := by
          have : 1 < span K := by omega
          exact h.2.2.2 this
        set A := span H
        set W := span K - 1
        set p := 2 ^ (verts H - 2)
        set q := 2 ^ (verts K - 2)
        have hp : 1 ≤ p := one_le_pow_two _
        have hq : 1 ≤ q := one_le_pow_two _
        have hT : A + 1 + max (A - 1) W + W ≤ 2 * (A + W) :=
          join_span_le_double sH hWpos
        have hAW : A + W ≤ p + q - 1 := by
          have : A ≤ p := ihH
          have : W ≤ q - 1 := Nat.sub_le_sub_right ihK 1
          have : p + (q - 1) = p + q - 1 := by omega
          omega
        have h2 : 2 * (A + W) ≤ 2 * (p + q - 1) := Nat.mul_le_mul_left 2 hAW
        have h3 : 2 * (p + q - 1) ≤ 2 * (p * q) :=
          Nat.mul_le_mul_left 2 (add_pred_le_mul hp hq)
        have h4 : 2 * (p * q) = 2 ^ (verts H + verts K - 3) := by
          have : verts H + verts K - 3 = 1 + (verts H - 2) + (verts K - 2) := by
            omega
          simp [p, q]
          rw [this, pow_add, pow_add, pow_one]
          ac_rfl
        have hv : verts H + verts K - 1 - 2 = verts H + verts K - 3 := by omega
        have : A + 1 + max (A - 1) W + W ≤ 2 ^ (verts H + verts K - 3) :=
          ((hT.trans h2).trans h3).trans_eq h4
        simpa [hv, A, W] using this

end Span
