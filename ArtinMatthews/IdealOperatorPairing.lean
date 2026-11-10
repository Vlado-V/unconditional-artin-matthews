module

public import ArtinMatthews.IdealLabelPairing
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

/-! A symmetric pairing estimate gives the corresponding energy
estimate for the actual symmetric output of an ideal operator. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelNorm_sq {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (f : MarkedPhysicalMarking P M → ℂ) :
    (idealLabelNorm P f)^2=idealLabelEnergy P M f := by
  rw [idealLabelNorm_eq_weighted P hV,idealWeightedVector_norm_sq P hV]

theorem idealLabelPairing_self_norm {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (f : MarkedPhysicalMarking P M → ℂ) :
    ‖idealLabelPairing P f f‖=idealLabelEnergy P M f := by
  rw [idealLabelPairing_inner P hV,inner_self_eq_norm_sq_to_K,norm_pow,
    RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),idealWeightedVector_norm_sq P hV]

theorem idealOperator_energy_of_symmetric_pairings {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (T : (MarkedPhysicalMarking P M → ℂ) → MarkedPhysicalMarking P M → ℂ)
    (hsym : ∀ f,IdealSymmetric f → IdealSymmetric (T f))
    {η : ℝ} (hη : 0 ≤ η)
    (hpair : ∀ f g,IdealSymmetric f → IdealSymmetric g →
      ‖idealLabelPairing P f (T g)‖ ≤ η*idealLabelNorm P f*idealLabelNorm P g)
    (f : MarkedPhysicalMarking P M → ℂ) (hf : IdealSymmetric f) :
    idealLabelEnergy P M (T f) ≤ η^2*idealLabelEnergy P M f := by
  have hsq := hpair (T f) f (hsym f hf) hf
  rw [idealLabelPairing_self_norm P hV,← idealLabelNorm_sq P hV] at hsq
  have ho : 0 ≤ idealLabelNorm P (T f) := Real.sqrt_nonneg _
  have hi : 0 ≤ idealLabelNorm P f := Real.sqrt_nonneg _
  have hnorm : idealLabelNorm P (T f) ≤ η*idealLabelNorm P f := by
    by_cases hz : idealLabelNorm P (T f)=0
    · rw [hz]
      exact mul_nonneg hη hi
    · have hp : 0 < idealLabelNorm P (T f) := lt_of_le_of_ne ho (Ne.symm hz)
      nlinarith
  calc
    _ = (idealLabelNorm P (T f))^2 := (idealLabelNorm_sq P hV _).symm
    _ ≤ (η*idealLabelNorm P f)^2 := pow_le_pow_left₀ ho hnorm 2
    _ = _ := by rw [mul_pow,idealLabelNorm_sq P hV]

end
end ArtinMatthews
