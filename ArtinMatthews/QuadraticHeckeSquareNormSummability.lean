module

public import ArtinMatthews.QuadraticHeckeDualProfile
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries
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

/-- Absolute square-norm summability from an actual positive-axis power bound. -/
theorem quadraticHeckeSquareNorm_summable_of_power_bound
    (v : ℝ → ℂ) {a C X : ℝ} (ha : 1 < 2 * a) (hX : 0 < X)
    (hb : ∀ x : ℝ, 0 < x → ‖v x‖ ≤ C * x ^ (-a)) :
    Summable (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} =>
      ‖v (((Ideal.absNorm J.val : ℝ) / X) ^ 2)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun J => ?_)
    ((quadraticHeckePrincipalIdealNorm_summable F ha).mul_left (C * X ^ (2 * a)))
  have hq := quadraticHeckePrincipalIdealNorm_pos F J
  have hx := div_pos hq hX
  have h := hb (((Ideal.absNorm J.val : ℝ) / X) ^ 2) (sq_pos_of_pos hx)
  convert h using 1
  rw [← Real.rpow_natCast_mul hx.le 2 (-a)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * -a = -(2 * a) by ring,
    Real.div_rpow hq.le hX.le, Real.rpow_neg hX.le, div_inv_eq_mul]
  ring

theorem quadraticHeckeDualSquareNorm_summable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {X : ℝ} (hX : 0 < X) :
    Summable (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} =>
      ‖quadraticHeckeDualProfile A r w (((Ideal.absNorm J.val : ℝ) / X) ^ 2)‖) := by
  obtain ⟨C, _, hb⟩ := quadraticHeckeDualProfile_power_bound A r w hc hp hs
    (σ := 1) (by norm_num)
  exact quadraticHeckeSquareNorm_summable_of_power_bound F _
    (by norm_num : 1 < 2 * (1 : ℝ)) hX hb

end
end ArtinMatthews
