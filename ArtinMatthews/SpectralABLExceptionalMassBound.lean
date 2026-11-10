module

public import ArtinMatthews.SpectralABLExceptionalBound
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralABLWindowFirstMoments
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem spectralABLExceptionalWindowReal_first_moment_bound
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) {t : ℝ} (ht : 0 ≤ t) :
    t * spectralABLExceptionalWindowReal a A t ≤
      spectralABLExceptionalBound A * (1 + t ^ 2)⁻¹ := by
  let B : ℝ := spectralABLExceptionalBound A
  have hB : 0 ≤ B := by dsimp [B, spectralABLExceptionalBound]; positivity
  let u : ℝ := 1 + t ^ 2
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : 1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg t]
  have htu : t ≤ u := by dsimp [u]; nlinarith [sq_nonneg (t - 1)]
  have hpow : u ^ 2 ≤ u ^ (A - 1) := pow_le_pow_right₀ hu1 (by omega)
  have hdecay := spectralABLExceptionalWindowReal_decay a (show 1 ≤ A by omega) t
  change t * spectralABLExceptionalWindowReal a A t ≤ B * u⁻¹
  calc
    _ ≤ t * (B / u ^ (A - 1)) := mul_le_mul_of_nonneg_left hdecay ht
    _ ≤ t * (B / u ^ 2) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hB (pow_pos hu _) hpow) ht
    _ = (B / u) * (t / u) := by field_simp
    _ ≤ (B / u) * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one hu).mpr htu) (div_nonneg hB hu.le)
    _ = B * u⁻¹ := by simp [div_eq_mul_inv]

theorem spectralABLExceptionalWindowReal_first_moment_integral_le
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    (∫ t : ℝ in Ioi 0, t * spectralABLExceptionalWindowReal a A t) ≤
      spectralABLExceptionalBound A * (Real.pi / 2) := by
  have hleft := spectralABLExceptionalWindowReal_first_moment_integrable a hA
  have hright : IntegrableOn
      (fun t : ℝ => spectralABLExceptionalBound A * (1 + t ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul (spectralABLExceptionalBound A)).integrableOn
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, spectralABLExceptionalBound A * (1 + t ^ 2)⁻¹ := by
      apply integral_mono_ae hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact spectralABLExceptionalWindowReal_first_moment_bound a hA ht.le
    _ = spectralABLExceptionalBound A * (Real.pi / 2) := by
      rw [integral_const_mul]
      simp only [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]

end
end ArtinMatthews
