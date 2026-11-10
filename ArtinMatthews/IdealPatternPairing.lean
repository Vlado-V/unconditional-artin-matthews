module

public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealPatternProducts
public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.IdealPatternExpectation
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

/-! Pairing the actual copied/fresh row gives its literal auxiliary
average and two full product-label expectations. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealPatternPairing_expectation {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (C : G → Finset (Fin k)) (Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) C Θ ζ K g)=
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,(giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
        idealLabelExpectation P (k+ell) (fun a => idealLabelExpectation P (k+ell) (fun b =>
          star (f a)*K a (idealMix (idealPatternFreeCoordinates C) a b) aux*
            idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux)*
            g (idealMix (idealPatternFreeCoordinates C) a b))) := by
  unfold idealLabelPairing
  simp_rw [idealPatternApply_expectation P hV]
  unfold idealLabelExpectation idealDilationPhase
  simp only [mul_sum,RCLike.algebraMap_eq_ofReal]
  rw [sum_comm]
  apply sum_congr rfl
  intro aux _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  have hcast (r : ℝ) : (RCLike.ofReal r : ℂ)=Complex.ofReal r := rfl
  simp only [hcast]
  ring

end
end ArtinMatthews
