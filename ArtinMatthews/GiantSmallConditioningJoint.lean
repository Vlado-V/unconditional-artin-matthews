module

public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantSmallBilinearNormalization
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

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

/-- Both tail sums and both real damping factors in the conditioned pair. -/
theorem giantSmallConditioningMap_pair
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (q₁ q₂ : ℝ)
    (d : MarkedPhysicalMarking P k)
    (w₁ w₂ : GiantTwoSidedResidueState P (k + ell) → ℂ)
    (y y' : GiantTwoSidedFullResidue P) (H : ℂ) :
    star (giantSmallConditioningMap P k ell q₁ d w₁ y) * H *
        giantSmallConditioningMap P k ell q₂ d w₂ y' =
      ∑ r : MarkedPhysicalMarking P ell, ∑ r' : MarkedPhysicalMarking P ell,
        (((markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
            giantSmallTailMass P ell) *
          giantTwoSidedResidueDamping P (k + ell) q₁ y *
          giantTwoSidedResidueDamping P (k + ell) q₂ y' : ℝ) : ℂ) *
        star (giantSmallStateValue w₁ y (giantSmallAppend d r)) * H *
          giantSmallStateValue w₂ y' (giantSmallAppend d r') := by
  classical
  have hreal (t : ℝ) : star (t : ℂ) = (t : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  have hN : (giantSmallConditioningNormalization P k ell : ℂ) ^ 2 =
      ((markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
        giantSmallTailMass P ell : ℝ) : ℂ) := by
    exact_mod_cast giantSmallConditioningNormalization_sq hV
  calc
    _ = ∑ r : MarkedPhysicalMarking P ell, ∑ r' : MarkedPhysicalMarking P ell,
        ((giantSmallConditioningNormalization P k ell : ℂ) ^ 2 *
          (giantTwoSidedResidueDamping P (k + ell) q₁ y : ℂ) *
          (giantTwoSidedResidueDamping P (k + ell) q₂ y' : ℂ)) *
        star (giantSmallStateValue w₁ y (giantSmallAppend d r)) * H *
          giantSmallStateValue w₂ y' (giantSmallAppend d r') := by
      unfold giantSmallConditioningMap
      simp only [star_mul, star_sum, hreal, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro r' _
      ring
    _ = _ := by
      rw [hN]
      simp only [Complex.ofReal_mul]

variable {X Y : Type*} [Fintype X] [Fintype Y]
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]

/-- The finite conditioned bilinear form equals its original small-state tail expansion. -/
theorem giantSmallConditioning_joint_eq
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (q : ℝ)
    (w₁ : X → GiantTwoSidedResidueState P (k + ell) → ℂ)
    (w₂ : Y → GiantTwoSidedResidueState P (k + ell) → ℂ)
    (H : MarkedPhysicalMarking P k → GiantTwoSidedFullResidue P → X →
      GiantTwoSidedFullResidue P → Y → ℂ) :
    (∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
      ∑ x : X, ∑ y' : GiantTwoSidedFullResidue P, ∑ x' : Y,
        (((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹) : ℂ) *
          star (giantSmallConditioningMap P k ell q d (w₁ x) y) * H d y x y' x' *
            giantSmallConditioningMap P k ell q d (w₂ x') y') =
      ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
      ∑ x : X, ∑ y' : GiantTwoSidedFullResidue P, ∑ x' : Y,
      ∑ r : MarkedPhysicalMarking P ell, ∑ r' : MarkedPhysicalMarking P ell,
        (((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ *
          (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
            giantSmallTailMass P ell) *
          giantTwoSidedResidueDamping P (k + ell) q y *
          giantTwoSidedResidueDamping P (k + ell) q y' : ℝ) : ℂ) *
          star (giantSmallStateValue (w₁ x) y (giantSmallAppend d r)) * H d y x y' x' *
            giantSmallStateValue (w₂ x') y' (giantSmallAppend d r') := by
  classical
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y' _
  apply Finset.sum_congr rfl
  intro x' _
  calc
    _ = (((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹) : ℂ) *
        (star (giantSmallConditioningMap P k ell q d (w₁ x) y) * H d y x y' x' *
          giantSmallConditioningMap P k ell q d (w₂ x') y') := by ring
    _ = _ := by
      rw [giantSmallConditioningMap_pair hV q q]
      simp only [Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_inv]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro r' _
      ring

/-- The same finite identity with the combined normalization exponent displayed. -/
theorem giantSmallConditioning_joint_product_eq
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (q : ℝ)
    (w₁ : X → GiantTwoSidedResidueState P (k + ell) → ℂ)
    (w₂ : Y → GiantTwoSidedResidueState P (k + ell) → ℂ)
    (H : MarkedPhysicalMarking P k → GiantTwoSidedFullResidue P → X →
      GiantTwoSidedFullResidue P → Y → ℂ) :
    (∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
      ∑ x : X, ∑ y' : GiantTwoSidedFullResidue P, ∑ x' : Y,
        (((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹) : ℂ) *
          star (giantSmallConditioningMap P k ell q d (w₁ x) y) * H d y x y' x' *
            giantSmallConditioningMap P k ell q d (w₂ x') y') =
      ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
      ∑ x : X, ∑ y' : GiantTwoSidedFullResidue P, ∑ x' : Y,
      ∑ r : MarkedPhysicalMarking P ell, ∑ r' : MarkedPhysicalMarking P ell,
        (((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ *
          (∏ j, (bandReciprocalMass (P j)) ^ (-((k + ell : ℕ) : ℝ) - (ell : ℝ))) *
          giantTwoSidedResidueDamping P (k + ell) q y *
          giantTwoSidedResidueDamping P (k + ell) q y' : ℝ) : ℂ) *
          star (giantSmallStateValue (w₁ x) y (giantSmallAppend d r)) * H d y x y' x' *
            giantSmallStateValue (w₂ x') y' (giantSmallAppend d r') := by
  rw [giantSmallConditioning_joint_eq hV q w₁ w₂ H, giantSmallMass_mul_tailMass]

end
end ArtinMatthews
