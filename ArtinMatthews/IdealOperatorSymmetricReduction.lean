module

public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.IdealSlotPairing
public import ArtinMatthews.IdealSlotSymmetry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal endpoint symmetrizations extend a bound on symmetric
vectors to the full original harmonic Hilbert space. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealOperatorWithLaws_input_average {I G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (freshLaw auxLaw : ∀ j,↥(P j) → ℝ)
    (patterns : Finset I) (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K (idealSlotAverage f)=
      idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f := by
  unfold idealOperatorWithLaws
  rw [idealSlotAverage_fixed _ (idealSlotAverage_symmetric f)]

theorem idealOperatorWithLaws_energy_from_symmetric {I G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (freshLaw auxLaw : ∀ j,↥(P j) → ℝ) (patterns : Finset I)
    (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ f,IdealSymmetric f →
      idealLabelEnergy P (k+ell) (idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f) ≤
        B*idealLabelEnergy P (k+ell) f)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell) (idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f) ≤
      B*idealLabelEnergy P (k+ell) f := by
  rw [← idealOperatorWithLaws_input_average freshLaw auxLaw patterns C Θ ζ K f]
  exact (hbound (idealSlotAverage f) (idealSlotAverage_symmetric f)).trans
    (mul_le_mul_of_nonneg_left (idealSlotAverage_energy_le P hV f) hB)

end
end ArtinMatthews
