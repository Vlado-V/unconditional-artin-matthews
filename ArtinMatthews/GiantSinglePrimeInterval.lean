module

public import ArtinMatthews.GiantSinglePrimeLifespan
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Support and interval formulas for single-prime lifespans

Every active visit lies between the selected endpoints. The scalar weight
uses precisely the strictly internal unmarked damping factors and the two
optional negative ghost coefficients. Orphan endpoints are strictly ordered.
-/

namespace ArtinMatthews

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Restricting the unmarked product to a lifespan splits it at the first
and last active visits. -/
theorem giantSignedPrimeInterval_product {n : ℕ} (A : Finset (Fin n))
    (hA : A.Nonempty) (l u : Fin n) (hl : l ≤ A.min' hA) (hu : A.max' hA ≤ u)
    (f : Fin n → ℝ) :
    (∏ i ∈ Finset.univ.filter (fun i => l < i ∧ i < u ∧ i ∉ A), f i) =
      (∏ i ∈ Finset.univ.filter (fun i => l < i ∧ i < A.min' hA), f i) *
      (∏ i ∈ Finset.univ.filter (fun i => A.min' hA < i ∧ i < A.max' hA ∧ i ∉ A), f i) *
      (∏ i ∈ Finset.univ.filter (fun i => A.max' hA < i ∧ i < u), f i) := by
  let s := Finset.univ.filter (fun i : Fin n => l < i ∧ i < u)
  have haz := A.min'_le_max' hA
  have hs : s \ A = Finset.univ.filter (fun i => l < i ∧ i < u ∧ i ∉ A) := by
    ext i
    simp only [s, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hb : s.filter (fun i => i < A.min' hA) =
      Finset.univ.filter (fun i => l < i ∧ i < A.min' hA) := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hli, _⟩, hia⟩
      exact ⟨hli, hia⟩
    · rintro ⟨hli, hia⟩
      exact ⟨⟨hli, hia.trans_le (haz.trans hu)⟩, hia⟩
  have hm : s.filter (fun i => A.min' hA < i ∧ i < A.max' hA ∧ i ∉ A) =
      Finset.univ.filter (fun i => A.min' hA < i ∧ i < A.max' hA ∧ i ∉ A) := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hi => hi.2
    · rintro ⟨hai, hiz, hiA⟩
      exact ⟨⟨hl.trans_lt hai, hiz.trans_le hu⟩, hai, hiz, hiA⟩
  have he : s.filter (fun i => A.max' hA < i) =
      Finset.univ.filter (fun i => A.max' hA < i ∧ i < u) := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hiu⟩, hzi⟩
      exact ⟨hzi, hiu⟩
    · rintro ⟨hzi, hiu⟩
      exact ⟨⟨(hl.trans haz).trans_lt hzi, hiu⟩, hzi⟩
  have hprod := giantSignedPrimeInactive_product s A hA f
  rwa [hs, hb, hm, he] at hprod

/-- A chosen active lifespan uses only its endpoints, its active visits,
and strictly internal unmarked visits. -/
theorem giantSignedPrimeActiveEndpointWeight_interval (p : ℕ) {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA) :
    giantSignedPrimeActiveEndpointWeight p h q A hA c =
      if GiantSignedPrimeActiveCompatible p h A (A.min' hA) then
        giantSignedPrimeBirthCoefficient p h q (A.min' hA) c.1 *
          giantSignedPrimeTerminationCoefficient p h q (A.min' hA) (A.max' hA) c.2 *
          ∏ i ∈ Finset.univ.filter (fun i =>
            giantSignedPrimeStart (A.min' hA) c.1 < i ∧
              i < giantSignedPrimeEnd (A.max' hA) c.2 ∧ i ∉ A),
            giantSignedPrimeDamping p h q i (A.min' hA)
      else 0 := by
  rw [giantSignedPrimeInterval_product A hA _ _
    (giantSignedPrimeStart_le _ _) (giantSignedPrimeEnd_ge _ _)]
  unfold giantSignedPrimeActiveEndpointWeight giantSignedPrimePrefixWeight giantSignedPrimeSuffixWeight
  split_ifs <;> ring

/-- Nonzero active weights retain the common active offset. -/
theorem giantSignedPrimeActiveEndpointWeight_compatible (p : ℕ) {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA)
    (hc : giantSignedPrimeActiveEndpointWeight p h q A hA c ≠ 0) :
    GiantSignedPrimeActiveCompatible p h A (A.min' hA) := by
  by_contra hbad
  exact hc (by simp only [giantSignedPrimeActiveEndpointWeight, hbad, ite_false])

/-- Both endpoints of every nonzero active lifespan have the common
active residue, including genuine ghost endpoints. -/
theorem giantSignedPrimeActiveEndpointWeight_endpoints (p : ℕ) {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA)
    (hc : giantSignedPrimeActiveEndpointWeight p h q A hA c ≠ 0) :
    (h (giantSignedPrimeStart (A.min' hA) c.1) : ZMod p) = (h (A.min' hA) : ZMod p) ∧
      (h (giantSignedPrimeEnd (A.max' hA) c.2) : ZMod p) = (h (A.min' hA) : ZMod p) := by
  have hcompatible := giantSignedPrimeActiveEndpointWeight_compatible p h q A hA c hc
  constructor
  · cases heq : c.1 with
    | none => simp only [giantSignedPrimeStart]
    | some l =>
      change (h l.1 : ZMod p) = _
      by_contra hbad
      have hz : giantSignedPrimePrefixWeight p h q (A.min' hA) c.1 = 0 := by
        simp only [giantSignedPrimePrefixWeight, heq, giantSignedPrimeBirthCoefficient,
          giantSignedPrimeOffsetHit, hbad, ite_false, mul_zero, zero_mul]
      exact hc (by simp only [giantSignedPrimeActiveEndpointWeight, hcompatible,
        ite_true, hz, zero_mul])
  · cases heq : c.2 with
    | none =>
      simp only [giantSignedPrimeEnd]
      exact hcompatible _ (A.max'_mem hA)
    | some u =>
      change (h u.1 : ZMod p) = _
      by_contra hbad
      have hz : giantSignedPrimeSuffixWeight p h q (A.min' hA) (A.max' hA) c.2 = 0 := by
        simp only [giantSignedPrimeSuffixWeight, heq, giantSignedPrimeTerminationCoefficient,
          giantSignedPrimeOffsetHit, hbad, ite_false, mul_zero, zero_mul]
      exact hc (by simp only [giantSignedPrimeActiveEndpointWeight, hcompatible,
        ite_true, hz, mul_zero])

abbrev GiantSignedPrimeOrphanEndpointChoice (n : ℕ) :=
  Σ l : Fin n, ↥(Finset.univ.filter (fun u : Fin n => l < u))

def giantSignedPrimeOrphanEndpointWeight (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (c : GiantSignedPrimeOrphanEndpointChoice n) : ℝ :=
  giantSignedPrimeOrphanWeight p h q c.1 c.2.1

theorem giantSignedPrimeOrphanEndpoint_strict {n : ℕ}
    (c : GiantSignedPrimeOrphanEndpointChoice n) : c.1 < c.2.1 :=
  (Finset.mem_filter.mp c.2.2).2

theorem giantSignedPrimeOrphanEndpointWeight_sum (p : ℕ) {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) :
    (∑ c : GiantSignedPrimeOrphanEndpointChoice n,
      giantSignedPrimeOrphanEndpointWeight p h q c) =
      ∑ l : Fin n, ∑ u ∈ Finset.univ.filter (fun u => l < u),
        giantSignedPrimeOrphanWeight p h q l u := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l _
  exact Finset.sum_coe_sort (s := Finset.univ.filter (fun u : Fin n => l < u))
    (f := fun u => giantSignedPrimeOrphanWeight p h q l u)

/-- Every nonzero orphan weight has equal endpoint residues. -/
theorem giantSignedPrimeOrphanEndpointWeight_endpoints (p : ℕ) {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (c : GiantSignedPrimeOrphanEndpointChoice n)
    (hc : giantSignedPrimeOrphanEndpointWeight p h q c ≠ 0) :
    (h c.2.1 : ZMod p) = (h c.1 : ZMod p) := by
  by_contra hbad
  exact hc (by simp only [giantSignedPrimeOrphanEndpointWeight,
    giantSignedPrimeOrphanWeight, giantSignedPrimeOffsetHit, hbad, ite_false, mul_zero, zero_mul])

/-- Inactive lifespans consist of the baseline and the finite family of
strict orphan intervals, with their single reciprocal-prime cost. -/
theorem giantSignedPrimeResidueExpectation_orphan_lifespans (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) :
    giantSignedPrimeResidueExpectation p h q ∅ = giantSignedPrimeResidueBaseline p q +
      (1 / (p : ℝ)) * ∑ c : GiantSignedPrimeOrphanEndpointChoice n,
        giantSignedPrimeOrphanEndpointWeight p h q c := by
  rw [giantSignedPrimeOrphanEndpointWeight_sum]
  exact giantSignedPrimeResidueExpectation_empty p h q

end
end ArtinMatthews
