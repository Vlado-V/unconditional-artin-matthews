module

public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantSmallConditioningNorm
public import ArtinMatthews.GiantTwoSidedPatternDamping
public import ArtinMatthews.GiantTwoSidedResidueInitialMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The small conditioning loss has a constant per group, chosen before
the copied-list length, and hence a fixed logarithmic exponent for the
actual candidate groups. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSmallResidueEnergy_primeProduct {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    (f : GiantTwoSidedFullResidue P → ℂ) :
    giantSmallResidueEnergy f =
      ((∏ p ∈ markedPhysicalBandPrimes P, p : ℕ) : ℝ)⁻¹ * ∑ y, ‖f y‖ ^ 2 := by
  rw [giantSmallResidueEnergy, giantTwoSidedFullResidue_card]

theorem giantSmallStateEnergy_primeProduct {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val] {k ell : ℕ}
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ) :
    giantSmallStateEnergy w =
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
        (((∏ p ∈ markedPhysicalBandPrimes P, p : ℕ) : ℝ)⁻¹ * ∑ s, ‖w s‖ ^ 2) := by
  unfold giantSmallStateEnergy giantTwoSidedResidueHaarStateMass
  ring

theorem exists_giantSmallConditioning_norm_bound {J : Type*} [Fintype J] [DecidableEq J]
    {q v : ℝ} (hq : 0 < q) (hq1 : q < 1) (hv : 0 < v) (ell : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (P : J → Finset ℕ),
      (∀ j p, p ∈ P j → p.Prime) → Pairwise (fun i j => Disjoint (P i) (P j)) →
      (∀ j, v ≤ bandReciprocalMass (P j)) →
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val := nz
      ∀ (k : ℕ) (w : GiantTwoSidedResidueState P (k + ell) → ℂ),
        (∑ d : MarkedPhysicalMarking P k,
          giantSmallResidueEnergy (giantSmallConditioningMap P k ell q d w)) ≤
          B ^ Fintype.card J * giantSmallStateEnergy w := by
  obtain ⟨B, hB, hb⟩ := exists_giantTwoSidedPattern_slot_bound hq hq1 hv ell
  refine ⟨B, hB, ?_⟩
  intro P hP hdis hV nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val := nz
  intro k w
  exact giantSmallConditioning_norm_sum hP hdis (fun j => hv.trans_le (hV j))
    hq hq1.le (zero_le_one.trans hB)
    (fun j z => hb _ z ell (hV j) le_rfl) w

theorem giantCandidateSmallConditioning_log_bound (ell : ℕ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val := nz
      ∀ (k : ℕ) (w : GiantTwoSidedResidueState P (k + ell) → ℂ),
        (∑ d : MarkedPhysicalMarking P k,
          giantSmallResidueEnergy (giantSmallConditioningMap P k ell q d w)) ≤
          (Real.log x) ^ C * giantSmallStateEnergy w := by
  let v := Real.log 2 / 2
  have hv : 0 < v := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨B, hB, hb⟩ := exists_giantTwoSidedPattern_slot_bound hq hq1 hv ell
  let C := giantCandidateGroupLogRate * Real.log B
  refine ⟨C, mul_nonneg (by unfold giantCandidateGroupLogRate; positivity)
    (Real.log_nonneg hB), ?_⟩
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually,
    giantCandidateSelectedGroups_exponential_cost_eventually B hB] with x hgeo hprime hcost
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val := nz
  intro k w
  have hP (j : S) (p : ℕ) (hp : p ∈ P j) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val, hp⟩)).1
  have hV (j : S) : 0 < bandReciprocalMass (P j) := hv.trans ((hgeo S).2.1 j).1
  have hpow : B ^ Fintype.card S ≤ (Real.log x) ^ C := by
    rw [Fintype.card_coe]
    exact hcost S
  have hw : 0 ≤ giantSmallStateEnergy w :=
    mul_nonneg (div_nonneg
      (prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _)
      (Nat.cast_nonneg _)) (sum_nonneg fun _ _ => sq_nonneg _)
  exact (giantSmallConditioning_norm_sum hP (hgeo S).1 hV hq hq1.le
    (zero_le_one.trans hB) (fun j z => hb _ z ell ((hgeo S).2.1 j).1.le le_rfl) w).trans
      (mul_le_mul_of_nonneg_right hpow hw)

theorem giantSmallConditioningMap_parameter_invariant {T J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (q : ℝ) (d : MarkedPhysicalMarking P k)
    (W : T → GiantTwoSidedResidueState P (k + ell) → ℂ) (e : T ≃ T)
    (hW : ∀ t s, W (e t) s = W t s) (t : T) :
    giantSmallConditioningMap P k ell q d (W (e t)) =
      giantSmallConditioningMap P k ell q d (W t) := by
  have h : W (e t) = W t := funext (hW t)
  rw [h]

end
end ArtinMatthews
