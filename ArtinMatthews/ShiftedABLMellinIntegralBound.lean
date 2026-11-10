module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.ShiftedABLMellinProfileDerivatives
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial losses in the two Mellin heights are integrated against
the actual Schwartz kernels. -/

noncomputable section
open MeasureTheory Set
namespace ArtinMatthews

theorem shiftedABLMellin_integral_bound (F : ℝ × ℝ → ℂ)
    (b1 b2 : SchwartzMap ℝ ℂ) (J : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, ‖F z‖ ≤ B*(1+|z.1|+|z.2|)^J) :
    ‖∫ z : ℝ × ℝ, F z*(b1 z.1*b2 z.2)‖ ≤
      B*(∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖)*(∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖) := by
  let w (z : ℝ × ℝ) := (1+|z.1|+|z.2|)^J*(‖b1 z.1‖*‖b2 z.2‖)
  obtain ⟨hw,hbound⟩ := shiftedABLMellin_product_moment_bound b1 b2 J
  have hpoint (z : ℝ × ℝ) : ‖F z*(b1 z.1*b2 z.2)‖ ≤ B*w z := by
    rw [norm_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_right (hF z) (by positivity)).trans_eq (by dsimp [w]; ring)
  calc
    _ ≤ ∫ z : ℝ × ℝ, B*w z :=
      norm_integral_le_of_norm_le (hw.const_mul B) (ae_of_all _ hpoint)
    _ = B*(∫ z : ℝ × ℝ, w z) := integral_const_mul B w
    _ ≤ B*((∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖)*(∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖)) :=
      mul_le_mul_of_nonneg_left hbound hB
    _ = _ := by ring

end ArtinMatthews
