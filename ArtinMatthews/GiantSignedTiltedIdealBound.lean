module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedIdealEnergySum
public import ArtinMatthews.GiantSignedIdealTiltError
public import ArtinMatthews.GiantSignedTiltDensity
public import ArtinMatthews.GiantSignedTiltDifference
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
public import Mathlib.Tactic.ENatToNat
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

/-! The original harmonic contraction transfers to the actual tilted
active and fresh laws with explicit density and coefficient errors. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedTiltedIdeal_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 1 ≤ r j p)
    (R : ℝ) (hR : 0 ≤ R) (hrR : ∀ j p, r j p ≤ R)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (η U : ℝ) (hη : 0 ≤ η) (hU : 0 ≤ U)
    (hFresh : ∀ v ∈ patterns, ∀ b : MarkedPhysicalMarking P (k+ell),
      idealFreshTargetMass r (C v) b ≤ 1 + η)
    (hOriginal : ∀ f : MarkedPhysicalMarking P (k+ell) → ℂ, IdealSymmetric f →
      idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
        U ^ 2 * idealLabelEnergy P (k+ell) f)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) :
    (∑ a, giantSignedActiveMass (fun j p => markedHarmonicAtom (P j) p * r j p) a *
      ‖idealOperatorWithLaws (fun j p => markedHarmonicAtom (P j) p * r j p)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K f a‖ ^ 2) ≤
      R ^ (Fintype.card J * (k+ell)) * (U + η * ∑ v ∈ patterns, cost v) ^ 2 *
        ∑ a, giantSignedActiveMass (fun j p => markedHarmonicAtom (P j) p * r j p) a * ‖f a‖ ^ 2 := by
  classical
  let μ : ∀ j, P j → ℝ := fun j => markedHarmonicAtom (P j)
  let T := idealOperatorWithLaws (fun j p => μ j p * r j p) μ patterns C Θ ζ K f
  let A := idealOperator patterns C Θ ζ K f
  let D := fun a => T a - A a
  let B := ∑ v ∈ patterns, cost v
  have hB : 0 ≤ B := Finset.sum_nonneg hcost
  have hμ (j : J) (p : P j) : 0 ≤ μ j p := markedHarmonicAtom_nonneg (P j) (hV j)
  have hD : idealLabelEnergy P (k+ell) D ≤ (η * B) ^ 2 * idealLabelEnergy P (k+ell) f :=
    giantSignedIdeal_tilt_error_energy hV hP r hr patterns C Θ ζ K cost hcost hK η hη hFresh f
  have hA := hOriginal f hf
  let g : Bool → MarkedPhysicalMarking P (k+ell) → ℂ := fun b => if b then A else D
  let c : Bool → ℝ := fun b => if b then U else η * B
  have hc (b : Bool) (_ : b ∈ (Finset.univ : Finset Bool)) : 0 ≤ c b := by
    cases b
    · change 0 ≤ η * B
      exact mul_nonneg hη hB
    · change 0 ≤ U
      exact hU
  have hg (b : Bool) (_ : b ∈ (Finset.univ : Finset Bool)) :
      idealLabelEnergy P (k+ell) (g b) ≤ (c b) ^ 2 * idealLabelEnergy P (k+ell) f := by
    cases b
    · exact hD
    · exact hA
  have hsum := giantSignedIdealEnergy_sum hV Finset.univ c hc f g hg
  have hgSum : (fun a => ∑ b : Bool, g b a) = T := by
    funext a
    simp [g, D]
  rw [hgSum] at hsum
  have hT : idealLabelEnergy P (k+ell) T ≤ (U + η * B) ^ 2 * idealLabelEnergy P (k+ell) f := by
    simpa [c, add_comm] using hsum
  have hout := giantSignedTilt_activeEnergy_le μ r hμ (fun j p => zero_le_one.trans (hr j p))
    R hrR T
  have hin := giantSignedTilt_originalEnergy_le μ r hμ hr f
  have hpR : 0 ≤ R ^ (Fintype.card J * (k+ell)) := pow_nonneg hR _
  change _ ≤ R ^ (Fintype.card J * (k+ell)) * (U + η * B) ^ 2 * _
  calc
    _ ≤ R ^ (Fintype.card J * (k+ell)) * idealLabelEnergy P (k+ell) T := hout
    _ ≤ R ^ (Fintype.card J * (k+ell)) * ((U + η * B) ^ 2 * idealLabelEnergy P (k+ell) f) :=
      mul_le_mul_of_nonneg_left hT hpR
    _ ≤ R ^ (Fintype.card J * (k+ell)) * ((U + η * B) ^ 2 *
        ∑ a, giantSignedActiveMass (fun j p => μ j p * r j p) a * ‖f a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin (sq_nonneg _)) hpR
    _ = _ := by ring

end
end ArtinMatthews
