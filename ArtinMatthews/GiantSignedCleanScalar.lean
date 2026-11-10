module

public import Mathlib.Basic.Real.Basic
public import ArtinMatthews.GiantSignedTiltError
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

/-! The exact density prefactor and the additive norm errors give the
source factor two once the actual errors are sufficiently small. -/
namespace ArtinMatthews
noncomputable section

theorem giantSignedCleanScalar_two
    (δ U E : ℝ) (dim : ℕ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hsmall : (dim : ℝ) * δ ≤ 1 / 2)
    (hU : 0 ≤ U) (hE : 0 ≤ E) (herr : E ≤ U / 4) :
    ((1 - δ)⁻¹) ^ dim * (U + E) ^ 2 ≤ (2 * U) ^ 2 := by
  have hR : ((1 - δ)⁻¹) ^ dim ≤ 2 := by
    have h := giantSignedTilt_inverse_pow_error δ hδ hδ1 dim hsmall
    linarith
  have hs : U + E ≤ (5 / 4 : ℝ) * U := by linarith
  have hsq := pow_le_pow_left₀ (add_nonneg hU hE) hs 2
  calc
    _ ≤ 2 * (U + E) ^ 2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
    _ ≤ 2 * ((5 / 4 : ℝ) * U) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ _ := by nlinarith [sq_nonneg U]

end
end ArtinMatthews
