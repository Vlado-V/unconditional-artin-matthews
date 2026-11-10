module

public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.GiantSignedFiniteTransport
public import ArtinMatthews.GiantSignedIdealResampling
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
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

/-! The literal copied/fresh transition preserves the harmonic product mass. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantSignedIdealTransition {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P (k+ell)) : ℝ :=
  if IdealCopied C a b then idealFreshTargetMass (fun j => markedHarmonicAtom (P j)) C b else 0

theorem giantSignedIdealTransition_average
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (F : MarkedPhysicalMarking P (k+ell) → ℝ) :
    (∑ b, giantSignedIdealTransition C a b * F b) =
      idealLabelExpectation P (k+ell) (fun z => F (idealMix (idealPatternFreeCoordinates C) a z)) := by
  have h := congrArg Complex.re (giantSignedIdeal_base_resampling hV C a (fun b => (F b : ℂ)))
  simpa [giantSignedIdealTransition, idealLabelExpectation, mul_ite, ite_mul, apply_ite] using h

theorem giantSignedIdealTransition_nonneg
    {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (a b : MarkedPhysicalMarking P (k+ell)) : 0 ≤ giantSignedIdealTransition C a b := by
  unfold giantSignedIdealTransition
  split_ifs
  · exact Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun _i _ =>
      markedHarmonicAtom_nonneg (P j) (hV j)
  · rfl

theorem giantSignedIdealTransition_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) : ∑ b, giantSignedIdealTransition C a b = 1 := by
  have h := giantSignedIdealTransition_average hV C a (fun _ => 1)
  simpa [idealLabelExpectation, idealLabelMass_sum P (k+ell) hV] using h

theorem giantSignedIdealTransition_preserves
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (F : MarkedPhysicalMarking P (k+ell) → ℝ) :
    (∑ a, idealLabelMass P (k+ell) a * ∑ b, giantSignedIdealTransition C a b * F b) =
      ∑ b, idealLabelMass P (k+ell) b * F b := by
  simp_rw [giantSignedIdealTransition_average hV C]
  exact idealLabelExpectation_mix (A := ℝ) P (k+ell) hV (idealPatternFreeCoordinates C) F

theorem giantSignedIdealTransition_stationary
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (b : MarkedPhysicalMarking P (k+ell)) :
    (∑ a, idealLabelMass P (k+ell) a * giantSignedIdealTransition C a b) =
      idealLabelMass P (k+ell) b := by
  have h := giantSignedIdealTransition_preserves hV C (fun z => if z = b then 1 else 0)
  simpa [mul_ite] using h

theorem giantSignedIdealTransition_energy
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (K : MarkedPhysicalMarking P (k+ell) → MarkedPhysicalMarking P (k+ell) → ℂ)
    (R : ℝ) (hK : ∀ a b, ‖K a b‖ ≤ R) (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ a, idealLabelMass P (k+ell) a *
      ‖∑ b, (giantSignedIdealTransition C a b : ℂ) * K a b * f b‖ ^ 2) ≤
        R ^ 2 * idealLabelEnergy P (k+ell) f :=
  giantSignedFiniteTransport_energy (idealLabelMass P (k+ell)) (idealLabelMass P (k+ell))
    (giantSignedIdealTransition C) (idealLabelMass_nonneg P (k+ell) hV)
    (giantSignedIdealTransition_nonneg hV C) (giantSignedIdealTransition_sum hV C)
    (giantSignedIdealTransition_stationary hV C) K R hK f

end
end ArtinMatthews
