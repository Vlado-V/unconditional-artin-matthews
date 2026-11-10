module

public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedIdealOperatorBound
public import ArtinMatthews.GiantSignedTiltDifference
public import ArtinMatthews.GiantSignedTiltOperator
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

/-! The fresh-law change is bounded in the original harmonic energy by
its derived coefficient error. Both endpoint slot averages are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdeal_tilt_error_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 1 ≤ r j p)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (η : ℝ) (hη : 0 ≤ η)
    (hFresh : ∀ v ∈ patterns, ∀ b : MarkedPhysicalMarking P (k+ell),
      idealFreshTargetMass r (C v) b ≤ 1 + η)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell)
      (fun a => idealOperatorWithLaws
        (fun j p => markedHarmonicAtom (P j) p * r j p)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K f a -
          idealOperator patterns C Θ ζ K f a) ≤
      (η * ∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  classical
  let D : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell := fun v a b aux =>
    K v a b aux * ((idealFreshTargetMass r (C v) b - 1 : ℝ) : ℂ)
  have hD (v : I) (hv : v ∈ patterns) (a b : MarkedPhysicalMarking P (k+ell))
      (aux : GiantTwoSidedPatternAuxiliary P (C v)) : ‖D v a b aux‖ ≤ η * cost v := by
    have he := idealTiltCoefficient_difference_norm r hr (C v) (K v) (1 + η) (hFresh v hv) a b aux
    rw [idealTiltCoefficient_difference] at he
    change ‖D v a b aux‖ ≤ _ at he
    have hc := mul_le_mul_of_nonneg_right (hK v hv a b aux) hη
    nlinarith
  have heq : (fun a => idealOperatorWithLaws
        (fun j p => markedHarmonicAtom (P j) p * r j p)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K f a -
          idealOperator patterns C Θ ζ K f a) = idealOperator patterns C Θ ζ D f := by
    funext a
    exact giantSignedIdeal_tilt_difference (fun j => markedHarmonicAtom (P j)) r patterns C Θ ζ K f a
  rw [heq]
  have he := giantSignedIdealOperator_absolute_energy hV hP patterns C Θ ζ D
    (fun v => η * cost v) (fun v hv => mul_nonneg hη (hcost v hv)) hD f
  simpa only [Finset.mul_sum] using he

end
end ArtinMatthews
