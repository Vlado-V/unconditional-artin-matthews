module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicThetaRationalScalars
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Rational diagonal scalars supplied by determinant-one congruence matrices. -/
noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped MatrixGroups
local notation "EO" => HeckeFamily.O

/-- The lower-right entry of a determinant-one matrix is invertible modulo
`(9A)` whenever its lower-left entry is divisible by `9A`. -/
theorem cubicTheta_lowerRight_isUnit (A : ℤ) (γ : SL(2, ℤ))
    (hc : 9 * A ∣ γ 1 0) :
    IsUnit (γ 1 1 : EO ⧸ cubicNumeratorHeckeModulus A) := by
  have hc0 : (γ 1 0 : EO ⧸ cubicNumeratorHeckeModulus A) = 0 := by
    change Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) (γ 1 0 : EO) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨k, hk⟩ := hc
    exact ⟨(k : EO), by exact_mod_cast hk⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hd : (γ 0 0 : EO ⧸ cubicNumeratorHeckeModulus A) *
      (γ 1 1 : EO ⧸ cubicNumeratorHeckeModulus A) = 1 := by
    have h := congrArg (Int.castRingHom (EO ⧸ cubicNumeratorHeckeModulus A)) hdet
    simpa only [Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hc0, mul_zero, sub_zero] using h
  exact IsUnit.of_mul_eq_one_right _ hd

/-- The actual rational-scalar eigenvalue is one for the congruence matrices
in the intended weight-one transformation law. -/
theorem cubicTheta_lowerRight_character_eq_one (A : ℤ) (hA : A ≠ 0)
    (γ : SL(2, ℤ)) (hc : 9 * A ∣ γ 1 0) :
    (cubicNumeratorHeckeCharacter A hA).residue
      (γ 1 1 : EO ⧸ cubicNumeratorHeckeModulus A) = 1 :=
  cubicNumeratorHeckeCharacter_residue_int A hA _ (cubicTheta_lowerRight_isUnit A γ hc)

end ArtinMatthews
