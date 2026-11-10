module

public import ArtinMatthews.GiantSignedIdealAuxiliary
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedIdealEnergySum
public import ArtinMatthews.GiantSignedIdealPatternBound
public import ArtinMatthews.IdealSlotSymmetry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual auxiliary expectation controls the ideal row while both
independent slot averages retain their original weights. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdealAveragedMultiplier_norm_le_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (a b : MarkedPhysicalMarking P (k+ell)) :
    ‖giantSignedIdealAveragedMultiplier C Θ ζ K a b‖ ≤
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux * ‖K a b aux‖ := by
  classical
  unfold giantSignedIdealAveragedMultiplier
  calc
    _ ≤ ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ‖(idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux : ℂ) * K a b aux *
          (((giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux : ℕ) : ℂ) ^
            ((ζ : ℂ) * Complex.I) *
            idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a *
              giantTwoSidedPatternAuxiliaryProduct aux))‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro aux _
      rw [norm_mul, norm_mul, giantSignedIdealMultiplier_norm hP,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (giantSignedIdealAuxiliaryMass_nonneg hV C aux), mul_one]

theorem giantSignedIdealPattern_expectation_energy
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (C : J → Finset (Fin k)) (Θ ζ R : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (hK : ∀ a b : MarkedPhysicalMarking P (k+ell),
      (∑ aux : GiantTwoSidedPatternAuxiliary P C,
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux * ‖K a b aux‖) ≤ R)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell)
        (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
          (fun j => markedHarmonicAtom (P j)) C Θ ζ K f) ≤
      R ^ 2 * idealLabelEnergy P (k+ell) f := by
  unfold idealLabelEnergy
  simp_rw [giantSignedIdealPattern_average_auxiliary]
  exact giantSignedIdealTransition_energy hV C
    (giantSignedIdealAveragedMultiplier C Θ ζ K) R
    (fun a b => (giantSignedIdealAveragedMultiplier_norm_le_sum hV hP C Θ ζ K a b).trans
      (hK a b)) f

theorem giantSignedIdealOperator_expectation_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hK : ∀ v ∈ patterns, ∀ a b : MarkedPhysicalMarking P (k+ell),
      (∑ aux : GiantTwoSidedPatternAuxiliary P (C v),
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux * ‖K v a b aux‖) ≤ cost v)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
      (∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  classical
  let μ : ∀ j, P j → ℝ := fun j => markedHarmonicAtom (P j)
  let T (v : I) := idealPatternApplyWithLaws μ μ (C v) Θ ζ (K v) (idealSlotAverage f)
  have heach (v : I) (hv : v ∈ patterns) :
      idealLabelEnergy P (k+ell) (T v) ≤ (cost v) ^ 2 *
        idealLabelEnergy P (k+ell) (idealSlotAverage f) :=
    giantSignedIdealPattern_expectation_energy hV hP (C v) Θ ζ (cost v) (K v) (hK v hv) _
  have hsum := giantSignedIdealEnergy_sum hV patterns cost hcost (idealSlotAverage f) T heach
  unfold idealOperator idealOperatorWithLaws
  calc
    _ ≤ idealLabelEnergy P (k+ell) (fun a => ∑ v ∈ patterns, T v a) :=
      idealSlotAverage_energy_le P hV _
    _ ≤ (∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) (idealSlotAverage f) := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left (idealSlotAverage_energy_le P hV f) (sq_nonneg _)

end
end ArtinMatthews
