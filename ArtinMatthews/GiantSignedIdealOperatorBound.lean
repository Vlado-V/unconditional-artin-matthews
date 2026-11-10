module

public import ArtinMatthews.IdealLabelOperator
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

/-! The actual two-sided slot average has the full coefficient-budget bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdealOperator_absolute_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
      (∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  classical
  let μ : ∀ j, P j → ℝ := fun j => markedHarmonicAtom (P j)
  let T (v : I) := idealPatternApplyWithLaws μ μ (C v) Θ ζ (K v) (idealSlotAverage f)
  have heach (v : I) (hv : v ∈ patterns) :
      idealLabelEnergy P (k+ell) (T v) ≤ (cost v) ^ 2 *
        idealLabelEnergy P (k+ell) (idealSlotAverage f) :=
    giantSignedIdealPattern_energy hV hP (C v) Θ ζ (cost v) (K v) (hK v hv) _
  have hsum := giantSignedIdealEnergy_sum hV patterns cost hcost (idealSlotAverage f) T heach
  unfold idealOperator idealOperatorWithLaws
  calc
    _ ≤ idealLabelEnergy P (k+ell) (fun a => ∑ v ∈ patterns, T v a) :=
      idealSlotAverage_energy_le P hV _
    _ ≤ (∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) (idealSlotAverage f) := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left (idealSlotAverage_energy_le P hV f) (sq_nonneg _)

end
end ArtinMatthews
