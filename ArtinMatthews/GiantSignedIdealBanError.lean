module

public import ArtinMatthews.GiantSignedAuxiliaryBan
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedIdealExpectationBound
public import ArtinMatthews.GiantSignedIdealLinearity
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

/-! The free/active exclusion error is averaged over the original
auxiliary draws before applying the actual ideal operator energy bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantSignedAuxiliaryExcludedCoefficient
    {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (K : GiantTwoSidedPatternCoefficient P C ell) :
    GiantTwoSidedPatternCoefficient P C ell :=
  fun a b aux => if GiantSignedAuxiliaryBan C a b aux then 0 else K a b aux

theorem giantSignedAuxiliaryExcluded_expectation
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (C : J → Finset (Fin k)) (K : GiantTwoSidedPatternCoefficient P C ell)
    (cost ε : ℝ) (hcost : 0 ≤ cost)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ cost)
    (hBan : ∀ a b : MarkedPhysicalMarking P (k+ell),
      (∑ aux : GiantTwoSidedPatternAuxiliary P C,
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (if GiantSignedAuxiliaryBan C a b aux then 0 else 1 : ℝ)) ≤ ε)
    (a b : MarkedPhysicalMarking P (k+ell)) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
        ‖giantSignedAuxiliaryExcludedCoefficient C K a b aux‖) ≤ cost * ε := by
  classical
  calc
    _ ≤ ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (cost * (if GiantSignedAuxiliaryBan C a b aux then 0 else 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro aux _
      apply mul_le_mul_of_nonneg_left _ (giantSignedIdealAuxiliaryMass_nonneg hV C aux)
      unfold giantSignedAuxiliaryExcludedCoefficient
      split_ifs
      · simp
      · simpa only [mul_one] using hK a b aux
    _ = cost * ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (if GiantSignedAuxiliaryBan C a b aux then 0 else 1 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro aux _
      ring
    _ ≤ cost * ε := mul_le_mul_of_nonneg_left (hBan a b) hcost

theorem giantSignedIdeal_ban_difference
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealOperator patterns C Θ ζ K f a -
      idealOperator patterns C Θ ζ
        (fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0) f a =
      idealOperator patterns C Θ ζ
        (fun v => giantSignedAuxiliaryExcludedCoefficient (C v) (K v)) f a := by
  classical
  have hcoeff : (fun v a b aux => K v a b aux -
      (if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0)) =
      (fun v => giantSignedAuxiliaryExcludedCoefficient (C v) (K v)) := by
    funext v a b aux
    unfold giantSignedAuxiliaryExcludedCoefficient
    by_cases h : GiantSignedAuxiliaryBan (C v) a b aux
    · simp only [h, ite_true, sub_self]
    · simp only [h, ite_false, sub_zero]
  have he := (giantSignedIdealOperator_sub (fun j => markedHarmonicAtom (P j))
    (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K
    (fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0)
    f a).symm
  rw [hcoeff] at he
  exact he

theorem giantSignedIdeal_ban_error_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost ε : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hε : ∀ v ∈ patterns, 0 ≤ ε v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (hBan : ∀ v ∈ patterns, ∀ a b : MarkedPhysicalMarking P (k+ell),
      (∑ aux : GiantTwoSidedPatternAuxiliary P (C v),
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (if GiantSignedAuxiliaryBan (C v) a b aux then 0 else 1 : ℝ)) ≤ ε v)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell)
      (fun a => idealOperator patterns C Θ ζ K f a -
        idealOperator patterns C Θ ζ
          (fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0) f a) ≤
      (∑ v ∈ patterns, cost v * ε v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  simp_rw [giantSignedIdeal_ban_difference]
  exact giantSignedIdealOperator_expectation_energy hV hP patterns C Θ ζ
    (fun v => giantSignedAuxiliaryExcludedCoefficient (C v) (K v))
    (fun v => cost v * ε v) (fun v hv => mul_nonneg (hcost v hv) (hε v hv))
    (fun v hv a b => giantSignedAuxiliaryExcluded_expectation hV (C v) (K v)
      (cost v) (ε v) (hcost v hv) (hK v hv) (hBan v hv) a b) f

end
end ArtinMatthews
