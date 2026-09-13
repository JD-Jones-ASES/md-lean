import Mathlib

namespace Span

lemma sq_sub_four {n : ℕ} (hn : 2 ≤ n) : (n - 2) * (n + 2) = n * n - 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp [Nat.mul_add, Nat.add_mul]
  omega

lemma two_m2_T_pow (n m T : ℕ) :
    (2 * m ^ 2 * T) ^ n = 2 ^ n * (m ^ 2) ^ n * T ^ n := by
  have h1 : 2 * m ^ 2 * T = (2 * m ^ 2) * T := by ring
  rw [h1, mul_pow, mul_pow]

theorem clearing_denom_le_of {n m T d : ℕ}
    (hn : 2 ≤ n) (hT : T ≤ 2 ^ (n - 2))
    (hd : d ≤ (2 * m ^ 2 * T) ^ n) :
    T ^ 2 * d ≤ 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) := by
  have hmul : T ^ 2 * d ≤ T ^ 2 * (2 * m ^ 2 * T) ^ n :=
    Nat.mul_le_mul_left _ hd
  have hrew : T ^ 2 * (2 * m ^ 2 * T) ^ n =
      2 ^ n * (m ^ 2) ^ n * T ^ (n + 2) := by
    rw [two_m2_T_pow]
    have : T ^ 2 * (2 ^ n * (m ^ 2) ^ n * T ^ n) =
        2 ^ n * (m ^ 2) ^ n * (T ^ 2 * T ^ n) := by ring
    rw [this, ← pow_add, Nat.add_comm 2 n]
  have hTpow : T ^ (n + 2) ≤ (2 ^ (n - 2)) ^ (n + 2) :=
    Nat.pow_le_pow_left hT (n + 2)
  have hpowmul : (2 ^ (n - 2)) ^ (n + 2) = 2 ^ ((n - 2) * (n + 2)) :=
    (Nat.pow_mul 2 (n - 2) (n + 2)).symm
  have hexp : (n - 2) * (n + 2) = n * n - 4 := sq_sub_four hn
  have hm2n : (m ^ 2) ^ n = m ^ (2 * n) :=
    (Nat.pow_mul m 2 n).symm
  have hmid : 2 ^ n * (m ^ 2) ^ n * T ^ (n + 2) ≤
      2 ^ n * m ^ (2 * n) * 2 ^ (n * n - 4) := by
    calc
      2 ^ n * (m ^ 2) ^ n * T ^ (n + 2) ≤
          2 ^ n * (m ^ 2) ^ n * (2 ^ (n - 2)) ^ (n + 2) :=
        Nat.mul_le_mul_left _ hTpow
      _ = 2 ^ n * m ^ (2 * n) * 2 ^ ((n - 2) * (n + 2)) := by
          rw [hpowmul, hm2n]
      _ = 2 ^ n * m ^ (2 * n) * 2 ^ (n * n - 4) := by
          rw [hexp]
  have hpowadd : 2 ^ n * 2 ^ (n * n - 4) = 2 ^ (n * n + n - 4) := by
    have : n + (n * n - 4) = n * n + n - 4 := by
      have : 4 ≤ n * n := Nat.mul_le_mul hn hn
      omega
    rw [← Nat.pow_add, this]
  have hswap : 2 ^ n * m ^ (2 * n) * 2 ^ (n * n - 4) =
      2 ^ (n * n + n - 4) * m ^ (2 * n) := by
    have : 2 ^ n * m ^ (2 * n) * 2 ^ (n * n - 4) =
        (2 ^ n * 2 ^ (n * n - 4)) * m ^ (2 * n) := by ring
    rw [this, hpowadd]
  have hn2exp : n * n + n - 4 = n ^ 2 + n - 4 := by rw [Nat.pow_two]
  calc
    T ^ 2 * d ≤ T ^ 2 * (2 * m ^ 2 * T) ^ n := hmul
    _ = 2 ^ n * (m ^ 2) ^ n * T ^ (n + 2) := hrew
    _ ≤ 2 ^ n * m ^ (2 * n) * 2 ^ (n * n - 4) := hmid
    _ = 2 ^ (n * n + n - 4) * m ^ (2 * n) := hswap
    _ = 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) := by rw [hn2exp]

theorem clearing_denom_le {n T d : ℕ}
    (hn : 2 ≤ n) (hT : T ≤ 2 ^ (n - 2))
    (hd : d ≤ (2 * n ^ 2 * T) ^ n) :
    T ^ 2 * d ≤ 2 ^ (n ^ 2 + n - 4) * n ^ (2 * n) :=
  clearing_denom_le_of hn hT hd

theorem clearing_denom_le_pred {n T d : ℕ}
    (hn : 2 ≤ n) (hT : T ≤ 2 ^ (n - 2))
    (hd : d ≤ (2 * (n - 1) ^ 2 * T) ^ n) :
    T ^ 2 * d ≤ 2 ^ (n ^ 2 + n - 4) * (n - 1) ^ (2 * n) :=
  clearing_denom_le_of hn hT hd

theorem clearing_grid_le_of {n m T d : ℕ}
    (hn : 2 ≤ n) (hT : T ≤ 2 ^ (n - 2))
    (hd : d ≤ (2 * m ^ 2 * T) ^ n) :
    T ^ 2 * d * T ≤ 2 ^ (n ^ 2 + 2 * n - 6) * m ^ (2 * n) := by
  have hQ := clearing_denom_le_of hn hT hd
  have h1 : T ^ 2 * d * T ≤ 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * T :=
    Nat.mul_le_mul_right T hQ
  have h2 : 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * T ≤
      2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * 2 ^ (n - 2) :=
    Nat.mul_le_mul_left _ hT
  have hadd : n * n + n - 4 + (n - 2) = n * n + 2 * n - 6 := by
    have : 4 ≤ n * n := Nat.mul_le_mul hn hn
    omega
  have hn2 : n ^ 2 = n * n := Nat.pow_two n
  have hpow : 2 ^ (n ^ 2 + n - 4) * 2 ^ (n - 2) =
      2 ^ (n ^ 2 + 2 * n - 6) := by
    rw [← Nat.pow_add, hn2, hadd, ← hn2]
  have hswap : 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * 2 ^ (n - 2) =
      2 ^ (n ^ 2 + 2 * n - 6) * m ^ (2 * n) := by
    have : 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * 2 ^ (n - 2) =
        (2 ^ (n ^ 2 + n - 4) * 2 ^ (n - 2)) * m ^ (2 * n) := by ring
    rw [this, hpow]
  calc
    T ^ 2 * d * T ≤ 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * T := h1
    _ ≤ 2 ^ (n ^ 2 + n - 4) * m ^ (2 * n) * 2 ^ (n - 2) := h2
    _ = 2 ^ (n ^ 2 + 2 * n - 6) * m ^ (2 * n) := hswap

theorem clearing_grid_le {n T d : ℕ}
    (hn : 2 ≤ n) (hT : T ≤ 2 ^ (n - 2))
    (hd : d ≤ (2 * n ^ 2 * T) ^ n) :
    T ^ 2 * d * T ≤ 2 ^ (n ^ 2 + 2 * n - 6) * n ^ (2 * n) :=
  clearing_grid_le_of hn hT hd

theorem clearing_grid_le_pred {n T d : ℕ}
    (hn : 2 ≤ n) (hT : T ≤ 2 ^ (n - 2))
    (hd : d ≤ (2 * (n - 1) ^ 2 * T) ^ n) :
    T ^ 2 * d * T ≤ 2 ^ (n ^ 2 + 2 * n - 6) * (n - 1) ^ (2 * n) :=
  clearing_grid_le_of hn hT hd

end Span
