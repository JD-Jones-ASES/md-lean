import Span

namespace MazurSpan

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

def joinCount : Scheme → ℕ
  | .edge => 0
  | .cycle _ => 0
  | .series A B => joinCount A + joinCount B
  | .join H K =>
      joinCount H + joinCount K + if 1 < span K then 1 else 0

def exactCap (n : ℕ) : ℕ :=
  if n % 2 = 0 then 2 ^ (n / 2) - 1 else 3 * 2 ^ ((n - 3) / 2) - 1

/-- Transfer: the two `Scheme` types are identical inductive trees. -/
def toSpan : Scheme → Span.Scheme
  | edge => .edge
  | cycle k => .cycle k
  | series A B => .series (toSpan A) (toSpan B)
  | join H K => .join (toSpan H) (toSpan K)

lemma verts_toSpan : ∀ s, verts s = Span.verts (toSpan s)
  | edge => rfl
  | cycle k => rfl
  | series A B => by simp [verts, Span.verts, toSpan, verts_toSpan A, verts_toSpan B]
  | join H K => by simp [verts, Span.verts, toSpan, verts_toSpan H, verts_toSpan K]

lemma span_toSpan : ∀ s, span s = Span.span (toSpan s)
  | edge => rfl
  | cycle k => rfl
  | series A B => by simp [span, Span.span, toSpan, span_toSpan A, span_toSpan B]
  | join H K => by
      simp [span, Span.span, toSpan, span_toSpan H, span_toSpan K]

lemma wf_toSpan : ∀ s, WellFormed s → Span.WellFormed (toSpan s)
  | edge, _ => trivial
  | cycle _, _ => trivial
  | series A B, h => ⟨wf_toSpan A h.1, wf_toSpan B h.2⟩
  | join H K, h => by
      refine ⟨wf_toSpan H h.1, wf_toSpan K h.2.1, ?_, ?_⟩
      · intro hs
        have hsK : span K = 1 := by simpa [span_toSpan K] using hs
        have h2 : verts K = 2 := h.2.2.1 hsK
        simpa [verts_toSpan K] using h2
      · intro hs
        have hsK : 1 < span K := by simpa [span_toSpan K] using hs
        have hHK := h.2.2.2 hsK
        simpa [verts_toSpan H, verts_toSpan K] using hHK

def fromSpan : Span.Scheme → Scheme
  | .edge => .edge
  | .cycle k => .cycle k
  | .series A B => .series (fromSpan A) (fromSpan B)
  | .join H K => .join (fromSpan H) (fromSpan K)

lemma verts_fromSpan : ∀ s, verts (fromSpan s) = Span.verts s
  | .edge => rfl
  | .cycle k => rfl
  | .series A B => by simp [verts, Span.verts, fromSpan, verts_fromSpan A, verts_fromSpan B]
  | .join H K => by simp [verts, Span.verts, fromSpan, verts_fromSpan H, verts_fromSpan K]

lemma span_fromSpan : ∀ s, span (fromSpan s) = Span.span s
  | .edge => rfl
  | .cycle k => rfl
  | .series A B => by simp [span, Span.span, fromSpan, span_fromSpan A, span_fromSpan B]
  | .join H K => by
      simp [span, Span.span, fromSpan, span_fromSpan H, span_fromSpan K]

lemma wf_fromSpan : ∀ s, Span.WellFormed s → WellFormed (fromSpan s)
  | .edge, _ => trivial
  | .cycle _, _ => trivial
  | .series A B, h => ⟨wf_fromSpan A h.1, wf_fromSpan B h.2⟩
  | .join H K, h => by
      refine ⟨wf_fromSpan H h.1, wf_fromSpan K h.2.1, ?_, ?_⟩
      · intro hs
        have hsK : Span.span K = 1 := by simpa [span_fromSpan K] using hs
        have h2 : Span.verts K = 2 := h.2.2.1 hsK
        simpa [verts_fromSpan K] using h2
      · intro hs
        have hsK : 1 < Span.span K := by simpa [span_fromSpan K] using hs
        have hHK := h.2.2.2 hsK
        simpa [verts_fromSpan H, verts_fromSpan K] using hHK

lemma joinCount_toSpan : ∀ s, joinCount s = Span.joinCount (toSpan s)
  | .edge => rfl
  | .cycle k => rfl
  | .series A B => by
      simp [joinCount, Span.joinCount, toSpan, joinCount_toSpan A, joinCount_toSpan B]
  | .join H K => by
      simp [joinCount, Span.joinCount, toSpan, joinCount_toSpan H, joinCount_toSpan K,
        span_toSpan K]

lemma joinCount_fromSpan : ∀ s, joinCount (fromSpan s) = Span.joinCount s
  | .edge => rfl
  | .cycle k => rfl
  | .series A B => by
      simp [joinCount, Span.joinCount, fromSpan, joinCount_fromSpan A, joinCount_fromSpan B]
  | .join H K => by
      simp [joinCount, Span.joinCount, fromSpan, joinCount_fromSpan H, joinCount_fromSpan K,
        span_fromSpan K]

lemma exactCap_eq (n : ℕ) : exactCap n = Span.exactCap n := rfl

theorem span_le_two_pow (s : Scheme) (h : WellFormed s) :
    span s ≤ 2 ^ (verts s - 2) := by
  have := Span.span_le_two_pow (toSpan s) (wf_toSpan s h)
  simpa [span_toSpan, verts_toSpan] using this

theorem span_le_exact (s : Scheme) (h : WellFormed s) :
    span s ≤ exactCap (verts s) := by
  have := Span.span_le_exact (toSpan s) (wf_toSpan s h)
  simpa [span_toSpan, verts_toSpan, exactCap_eq] using this

theorem exists_span_eq_exact (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Scheme, WellFormed s ∧ verts s = n ∧ span s = exactCap n := by
  obtain ⟨s, hwf, hv, hs⟩ := Span.exists_span_eq_exact n hn
  refine ⟨fromSpan s, wf_fromSpan s hwf, ?_, ?_⟩
  · simpa [verts_fromSpan] using hv
  · simpa [span_fromSpan, exactCap_eq] using hs

theorem span_succ_le_join_budget (s : Scheme) (h : WellFormed s) :
    span s + 1 ≤ 2 ^ joinCount s * (verts s - 2 * joinCount s) := by
  have := Span.span_succ_le_join_budget (toSpan s) (wf_toSpan s h)
  simpa [span_toSpan, verts_toSpan, joinCount_toSpan] using this

theorem exists_span_eq_join_budget (n j : ℕ)
    (h : n = 2 ∧ j = 0 ∨ 2 * j + 3 ≤ n) :
    ∃ s : Scheme, WellFormed s ∧ verts s = n ∧ joinCount s = j ∧
      span s + 1 = 2 ^ j * (n - 2 * j) := by
  obtain ⟨s, hwf, hv, hj, hs⟩ := Span.exists_span_eq_join_budget n j h
  refine ⟨fromSpan s, wf_fromSpan s hwf, ?_, ?_, ?_⟩
  · simpa [verts_fromSpan] using hv
  · simpa [joinCount_fromSpan] using hj
  · simpa [span_fromSpan] using hs

/-- The `(i, j)`-entry of an integer matrix. Named so compared
    statements do not apply a `Matrix` as a function; Palomar's
    core notation audit treats `Matrix` as an opaque type. -/
def entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℤ :=
  A i j

theorem natAbs_det_le_prod_rowSum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    A.det.natAbs ≤ ∏ i : Fin n, ∑ j : Fin n, (entry A i j).natAbs := by
  simpa [entry] using Span.natAbs_det_le_prod_rowSum n A

theorem natAbs_det_le_of_rowSum_le {n R : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i, ∑ j, (entry A i j).natAbs ≤ R) :
    A.det.natAbs ≤ R ^ n := by
  simpa [entry] using Span.natAbs_det_le_of_rowSum_le A (by simpa [entry] using h)

variable {n : ℕ}

def upwardSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then h t - h s else 0

def downwardSum (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then h s - h t else 0

def dartWeight (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (s t : Fin n) : ℕ :=
  if s = t then 0
  else if Adj s t = false then 0
  else if s ∈ B then 1
  else if h s < h t then downwardSum Adj h s
  else if h t < h s then upwardSum Adj h s
  else 0

def dirichlet (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun s t =>
    if s ∈ B then (if s = t then 1 else 0)
    else if s = t then ∑ u : Fin n, (dartWeight Adj h B s u : ℤ)
    else - (dartWeight Adj h B s t : ℤ)

lemma upwardSum_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    upwardSum Adj h s = Span.upwardSum Adj h s := rfl

lemma downwardSum_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    downwardSum Adj h s = Span.downwardSum Adj h s := rfl

lemma dartWeight_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (s t : Fin n) :
    dartWeight Adj h B s t = Span.dartWeight Adj h B s t := by
  simp [dartWeight, Span.dartWeight, upwardSum_eq, downwardSum_eq]

lemma dirichlet_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) :
    dirichlet Adj h B = Span.dirichlet Adj h B := by
  ext s t
  simp [dirichlet, Span.dirichlet, dartWeight_eq]

theorem dirichlet_rowSum_le {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hh : ∀ i, h i ≤ T) (hn : 2 ≤ n) (hT : 1 ≤ T) (s : Fin n) :
    ∑ t, (entry (dirichlet Adj h B) s t).natAbs ≤ 2 * (n - 1) ^ 2 * T := by
  simpa [dirichlet_eq, entry] using Span.dirichlet_rowSum_le Adj h B hh hn hT s

theorem dirichlet_det_le {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hh : ∀ i, h i ≤ T) (hn : 2 ≤ n) (hT : 1 ≤ T) :
    (dirichlet Adj h B).det.natAbs ≤ (2 * (n - 1) ^ 2 * T) ^ n := by
  simpa [dirichlet_eq] using Span.dirichlet_det_le Adj h B hh hn hT

theorem coord_denom {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hn : 2 ≤ n) (hTpos : 1 ≤ T) (hT : T ≤ 2 ^ (n - 2))
    (hh : ∀ i, h i ≤ T) :
    T ^ 2 * (dirichlet Adj h B).det.natAbs ≤
      2 ^ (n ^ 2 + n - 4) * (n - 1) ^ (2 * n) := by
  simpa [dirichlet_eq] using Span.coord_denom Adj h B hn hTpos hT hh

theorem coord_grid {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hn : 2 ≤ n) (hTpos : 1 ≤ T) (hT : T ≤ 2 ^ (n - 2))
    (hh : ∀ i, h i ≤ T) :
    T ^ 2 * (dirichlet Adj h B).det.natAbs * T ≤
      2 ^ (n ^ 2 + 2 * n - 6) * (n - 1) ^ (2 * n) := by
  simpa [dirichlet_eq] using Span.coord_grid Adj h B hn hTpos hT hh

def higherCount (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then (if h s < h t then 1 else 0) else 0

def lowerCount (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  ∑ t : Fin n, if Adj s t then (if h t < h s then 1 else 0) else 0

def dartMass (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) : ℕ :=
  higherCount Adj h s * downwardSum Adj h s +
    lowerCount Adj h s * upwardSum Adj h s

lemma higherCount_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    higherCount Adj h s = Span.higherCount Adj h s := rfl

lemma lowerCount_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    lowerCount Adj h s = Span.lowerCount Adj h s := rfl

lemma dartMass_eq (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (s : Fin n) :
    dartMass Adj h s = Span.dartMass Adj h s := by
  simp [dartMass, Span.dartMass, higherCount_eq, lowerCount_eq,
    upwardSum_eq, downwardSum_eq]

theorem dartMass_le {n T : ℕ} (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (hh : ∀ i, h i ≤ T) (s : Fin n) :
    dartMass Adj h s ≤ higherCount Adj h s * lowerCount Adj h s * T := by
  simpa [dartMass_eq, higherCount_eq, lowerCount_eq] using
    Span.dartMass_le Adj h hh s

theorem dartWeight_sum_eq_dartMass {n : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    {s : Fin n} (hs : s ∉ B) :
    ∑ t, dartWeight Adj h B s t = dartMass Adj h s := by
  simpa [dartWeight_eq, dartMass_eq] using
    Span.dartWeight_sum_eq_dartMass Adj h B hs

theorem dartWeight_interior_sum_le {n T : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ) (B : Finset (Fin n))
    (hh : ∀ i, h i ≤ T) {s : Fin n} (hs : s ∉ B) :
    ∑ t, dartWeight Adj h B s t ≤
      higherCount Adj h s * lowerCount Adj h s * T := by
  simpa [dartWeight_eq, higherCount_eq, lowerCount_eq] using
    Span.dartWeight_interior_sum_le Adj h B hh hs

def boundaryTarget (h : Fin n → ℕ) (T : ℕ) (B : Finset (Fin n)) : Fin n → ℤ :=
  fun s => if s ∈ B then (h s * (T - h s) : ℤ) else 0

lemma boundaryTarget_eq (h : Fin n → ℕ) (T : ℕ) (B : Finset (Fin n)) :
    boundaryTarget h T B = Span.boundaryTarget h T B := rfl

theorem dirichlet_adjugate_clears {n : ℕ}
    (Adj : Fin n → Fin n → Bool) (h : Fin n → ℕ)
    (B : Finset (Fin n)) (T : ℕ) :
    let M := dirichlet Adj h B
    let u := boundaryTarget h T B
    let z := M.adjugate.mulVec u
    M.mulVec z = M.det • u ∧
      ∀ s ∈ B, z s = M.det * (h s * (T - h s) : ℤ) := by
  intro M u z
  have hM : M = Span.dirichlet Adj h B := dirichlet_eq Adj h B
  have hu : u = Span.boundaryTarget h T B := boundaryTarget_eq h T B
  have := Span.dirichlet_adjugate_clears Adj h B T
  -- Unfold the let's in the Span theorem.
  simpa [M, u, z, hM, hu, dirichlet_eq] using this

end MazurSpan
