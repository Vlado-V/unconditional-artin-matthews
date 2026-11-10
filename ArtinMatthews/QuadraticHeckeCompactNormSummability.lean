module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries
public import ArtinMatthews.QuadraticHeckeSquareNormSummability
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
open NumberField Set MeasureTheory
open scoped NumberField ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem quadraticHeckeNorm_summable_of_power_bound
    (v : ℝ → ℂ) {a C X : ℝ} (ha : 1 < a) (hX : 0 < X)
    (hb : ∀ x : ℝ, 0 < x → ‖v x‖ ≤ C * x ^ (-a)) :
    Summable (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} =>
      ‖v ((Ideal.absNorm J.val : ℝ) / X)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun J => ?_)
    ((quadraticHeckePrincipalIdealNorm_summable F ha).mul_left (C * X ^ a))
  have hq := quadraticHeckePrincipalIdealNorm_pos F J
  have h := hb ((Ideal.absNorm J.val : ℝ) / X) (div_pos hq hX)
  convert h using 1
  rw [Real.div_rpow hq.le hX.le, Real.rpow_neg hX.le, div_inv_eq_mul]
  ring

theorem quadraticHeckeCompact_power_bound (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hs : Continuous w) (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → ‖w x‖ ≤ C * x ^ (-(n : ℝ)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ n * w x
  have hfc : Continuous f := by unfold f; fun_prop
  have hfs : HasCompactSupport f := hc.mul_left
  obtain ⟨C, hC⟩ := hfs.exists_bound_of_continuous hfc
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x
  change ‖(x : ℂ) ^ n * w x‖ ≤ C at h
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le] at h
  rw [Real.rpow_neg hx.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hx n)).mpr (by simpa only [mul_comm] using h)

theorem quadraticHeckeCompactNorm_summable (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hs : Continuous w) {X : ℝ} (hX : 0 < X) :
    Summable (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} =>
      ‖w ((Ideal.absNorm J.val : ℝ) / X)‖) := by
  obtain ⟨C, hC⟩ := quadraticHeckeCompact_power_bound w hc hs 2
  exact quadraticHeckeNorm_summable_of_power_bound F w (by norm_num : 1 < (2 : ℝ)) hX hC

theorem quadraticHeckeCompactSquareNorm_summable (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hs : Continuous w) {X : ℝ} (hX : 0 < X) :
    Summable (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} =>
      ‖w (((Ideal.absNorm J.val : ℝ) / X) ^ 2)‖) := by
  obtain ⟨C, hC⟩ := quadraticHeckeCompact_power_bound w hc hs 1
  exact quadraticHeckeSquareNorm_summable_of_power_bound F w (C := C)
    (by norm_num : 1 < 2 * (1 : ℝ)) hX (by simpa only [Nat.cast_one] using hC)

end
end ArtinMatthews
