module

public import ArtinMatthews.SourceComplexMellinSchwartz
public import ArtinMatthews.SourceComplexMellinWeight
public import ArtinMatthews.SourceComplexMellinAbsolute
public import ArtinMatthews.SourceComplexMellinEuler
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Function
open scoped SchwartzMap
noncomputable section

theorem sourceComplexMellin_iterate_euler (n : ℕ) (f : 𝓢(ℂ, ℂ)) (s : ℂ)
    (hs : 0 < s.re) :
    sourceComplexMellin ((sourceComplexEulerSchwartz^[n]) f) s =
      (-(2 * s)) ^ n * sourceComplexMellin f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', sourceComplexMellin_euler _ s hs, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

/-- Arbitrary vertical decay of the actual normalized complex-place Mellin integral,
uniformly on every closed strip in the positive half-plane. -/
theorem sourceComplexMellin_vertical_rapid (n : ℕ) (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ n * ‖sourceComplexMellin f s‖ ≤ C := by
  let g := (sourceComplexEulerSchwartz^[n]) f
  let B := ∫ z : ℂ, sourceComplexMellinMajorant g lo hi z ∂sourceComplexTraceMeasure
  let a := (1 + lo⁻¹) / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨a ^ n * max 0 B, mul_nonneg (pow_nonneg ha _) (le_max_left _ _), ?_⟩
  intro s hl hh
  have hs : 0 < s.re := hlo.trans_le hl
  have hB := sourceComplexMellin_norm_bound g lo hi s hlo hl hh
  have hnorm : ‖-(2 * s)‖ = 2 * ‖s‖ := by rw [norm_neg, norm_mul]; norm_num
  have hEuler : ‖sourceComplexMellin g s‖ =
      (2 * ‖s‖) ^ n * ‖sourceComplexMellin f s‖ := by
    dsimp [g]
    rw [sourceComplexMellin_iterate_euler n f s hs, norm_mul, norm_pow, hnorm]
  have hreal : lo ≤ ‖s‖ := hl.trans ((le_abs_self s.re).trans (Complex.abs_re_le_norm s))
  have h1 : 1 ≤ lo⁻¹ * ‖s‖ := by
    calc
      1 = lo⁻¹ * lo := (inv_mul_cancel₀ hlo.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hlo.le)
  have him : 1 + |s.im| ≤ a * (2 * ‖s‖) := by
    calc
      _ ≤ lo⁻¹ * ‖s‖ + ‖s‖ := add_le_add h1 (Complex.abs_im_le_norm s)
      _ = _ := by dsimp [a]; ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |s.im|) him n
  rw [mul_pow] at hp
  calc
    _ ≤ (a ^ n * (2 * ‖s‖) ^ n) * ‖sourceComplexMellin f s‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = a ^ n * ‖sourceComplexMellin g s‖ := by rw [hEuler, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB.trans (le_max_right 0 B)) (pow_nonneg ha _)

theorem sourceComplexTraceFourierMellin_vertical_rapid (n : ℕ)
    (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ n * ‖sourceComplexMellin (sourceComplexTraceFourier f) s‖ ≤ C := by
  have h := sourceComplexMellin_vertical_rapid n (sourceComplexTraceFourierSchwartz f) lo hi hlo
  have he : (sourceComplexTraceFourierSchwartz f : ℂ → ℂ) = sourceComplexTraceFourier f :=
    funext (sourceComplexTraceFourierSchwartz_apply f)
  rwa [he] at h

end
end ArtinMatthews.VaryingKummerAnalytic
