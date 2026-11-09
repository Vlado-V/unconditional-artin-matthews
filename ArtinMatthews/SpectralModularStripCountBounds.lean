module

public import Mathlib.NumberTheory.Modular


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative bottom-row bounds for actual modular transformations of a
point in the closed fundamental domain into a positive-height strip. -/
noncomputable section
open Set UpperHalfPlane
open scoped MatrixGroups
namespace ArtinMatthews

private theorem modular_strip_real_row_bound {x y c d B : ℝ}
    (hy : (1:ℝ)/2 ≤ y) (hB : 1 ≤ B) (hx : |x| ≤ (1:ℝ)/2)
    (hc : 1 ≤ c^2) (hD : (c*x+d)^2+(c*y)^2 < y*B) :
    |c| ≤ 2*B ∧ |d| ≤ 2*B := by
  have hyp : 0 < y := by linarith
  have hBp : 0 < B := by linarith
  have hcys : y^2 ≤ (c*y)^2 := by
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
    nlinarith
  have hyB : y < B := by
    apply (mul_lt_mul_iff_left₀ hyp).mp
    nlinarith [sq_nonneg (c*x+d)]
  have hDB : (c*x+d)^2+(c*y)^2 < B^2 :=
    hD.trans (by nlinarith)
  have hcy : |c| *y < B := by
    have hs : (|c| *y)^2 < B^2 := by
      rw [mul_pow,sq_abs]
      nlinarith [sq_nonneg (c*x+d)]
    nlinarith [mul_nonneg (abs_nonneg c) hyp.le]
  have hcB : |c| ≤ 2*B := by nlinarith [abs_nonneg c]
  have hcxB : |c*x+d| ≤ B := by
    have hs : |c*x+d| ^2 < B^2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (c*y)]
    nlinarith [abs_nonneg (c*x+d)]
  refine ⟨hcB,?_⟩
  calc
    |d| = |(c*x+d)-(c*x)| := by congr 1; ring
    _ ≤ |c*x+d| +|c*x| := by simpa only [Real.norm_eq_abs] using norm_sub_le (c*x+d) (c*x)
    _ = |c*x+d| +|c| *|x| := by rw [abs_mul]
    _ ≤ B+(2*B)*((1:ℝ)/2) :=
      add_le_add hcxB (mul_le_mul hcB hx (abs_nonneg _) (by positivity))
    _ = 2*B := by ring

theorem spectralModular_denom_normSq (g : SL(2,ℤ)) (z : UpperHalfPlane) :
    Complex.normSq (denom g z) =
      ((g 1 0 : ℝ)*z.re+(g 1 1 : ℝ))^2+((g 1 0 : ℝ)*z.im)^2 := by
  simp [ModularGroup.denom_apply,Complex.normSq_apply,pow_two]

theorem spectralModular_strip_bottom_row_bound (g : SL(2,ℤ))
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd)
    (Y : ℝ) (hY : 0 < Y) (hY1 : Y ≤ 1) (him : Y < (g • z).im) :
    |(g 1 0 : ℝ)| ≤ 2/Y ∧ |(g 1 1 : ℝ)| ≤ 2/Y := by
  have hB : 1 ≤ 1/Y := (le_div_iff₀ hY).mpr (by simpa using hY1)
  have hy : (1:ℝ)/2 ≤ z.im := by
    have hh := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith [z.im_pos]
  have htwo : 1 ≤ 2/Y := (le_div_iff₀ hY).mpr (by linarith)
  by_cases hc : g 1 0 = 0
  · have had : g 0 0*g 1 1 = 1 := by
      have hh := g.det_coe
      rw [Matrix.det_fin_two,hc] at hh
      simpa using hh
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨_,hd⟩ | ⟨_,hd⟩)
    · simp only [hc,hd,Int.cast_zero,abs_zero,Int.cast_one,abs_one]
      constructor <;> linarith
    · simp only [hc,hd,Int.cast_zero,abs_zero,Int.cast_neg,Int.cast_one,abs_neg,abs_one]
      constructor <;> linarith
  · have hc2 : 1 ≤ (g 1 0 : ℝ)^2 := by
      have hcases : g 1 0 ≤ -1 ∨ 1 ≤ g 1 0 := by omega
      rcases hcases with h | h
      · have hh : (g 1 0 : ℝ) ≤ -1 := by exact_mod_cast h
        nlinarith
      · have hh : 1 ≤ (g 1 0 : ℝ) := by exact_mod_cast h
        nlinarith
    have hp : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
    rw [ModularGroup.im_smul_eq_div_normSq] at him
    have hD : Complex.normSq (denom g z) < z.im/Y := by
      apply (lt_div_iff₀ hY).mpr
      simpa only [mul_comm] using (lt_div_iff₀ hp).mp him
    rw [spectralModular_denom_normSq] at hD
    have hh := modular_strip_real_row_bound hy hB hz.2 hc2 (by simpa [div_eq_mul_inv] using hD)
    simpa [div_eq_mul_inv] using hh

end ArtinMatthews
