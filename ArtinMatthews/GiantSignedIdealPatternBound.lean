module

public import ArtinMatthews.GiantSignedIdealTransition
public import ArtinMatthews.GiantSignedIdealAuxiliary
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Absolute energy of the actual ideal row, with its original auxiliary law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedIdealPattern_average_auxiliary
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
        (fun j => markedHarmonicAtom (P j)) C Θ ζ K f a =
      ∑ b : MarkedPhysicalMarking P (k+ell),
        (giantSignedIdealTransition C a b : ℂ) *
          giantSignedIdealAveragedMultiplier C Θ ζ K a b * f b := by
  classical
  unfold idealPatternApplyWithLaws giantSignedIdealAveragedMultiplier
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro aux _
  by_cases h : IdealCopied C a b
  · simp only [giantSignedIdealTransition, h, ite_true]
    ring
  · simp [giantSignedIdealTransition, h]

theorem giantSignedIdealPattern_energy
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (C : J → Finset (Fin k)) (Θ ζ R : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ R) (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell)
        (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
          (fun j => markedHarmonicAtom (P j)) C Θ ζ K f) ≤
      R ^ 2 * idealLabelEnergy P (k+ell) f := by
  unfold idealLabelEnergy
  simp_rw [giantSignedIdealPattern_average_auxiliary]
  exact giantSignedIdealTransition_energy hV C
    (giantSignedIdealAveragedMultiplier C Θ ζ K) R
    (giantSignedIdealAveragedMultiplier_norm hV hP C Θ ζ R K hK) f

end
end ArtinMatthews
