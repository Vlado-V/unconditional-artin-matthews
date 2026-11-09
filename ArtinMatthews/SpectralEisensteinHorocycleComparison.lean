module

public import ArtinMatthews.SpectralCuspEisensteinRowKernel
public import ArtinMatthews.SpectralGamma0EisensteinPlaneTerms


set_option backward.privateInPublic true
@[expose] public section

/-! A high-horocycle point is controlled by its genuine period average,
term by term. This avoids an assumed spectral or Fourier decay estimate. -/
noncomputable section
open Set
namespace ArtinMatthews

theorem eisensteinRowQuadratic_horizontal_compare (c d x t y : ℝ)
    (hy : 1 ≤ y) (hx : |x| ≤ 1) (ht : t ∈ Icc (0:ℝ) 1) :
    eisensteinRowQuadratic c d (t,y) ≤ 9*eisensteinRowQuadratic c d (x,y) := by
  have hxx : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
  have hdelta : (t-x)^2 ≤ 4 := by nlinarith [ht.1,ht.2]
  have hE : (c*(t-x))^2 ≤ 4*c^2 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hdelta)]
  have hB : c^2 ≤ (c*y)^2 := by
    nlinarith [mul_nonneg (sq_nonneg c) (show 0 ≤ y^2-1 by nlinarith)]
  have hA : (c*t+d)^2 ≤ 2*(c*x+d)^2+2*(c*(t-x))^2 := by
    nlinarith [sq_nonneg (c*x+d-c*(t-x))]
  dsimp [eisensteinRowQuadratic]
  nlinarith [sq_nonneg (c*x+d)]

theorem eisensteinRealRowTerm_horizontal_norm_compare (s : ℂ) (hs : 0 ≤ s.re)
    (c d x t y : ℝ) (hc : 0 < c) (hy : 1 ≤ y) (hx : |x| ≤ 1)
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖eisensteinRealRowTerm s c d x y‖ ≤ 9^s.re*‖eisensteinRealRowTerm s c d t y‖ := by
  have hyp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hqx := eisensteinRowQuadratic_pos c d (Or.inl hc.ne') (x,y) hyp
  have hqt := eisensteinRowQuadratic_pos c d (Or.inl hc.ne') (t,y) hyp
  have hQ := eisensteinRowQuadratic_horizontal_compare c d x t y hy hx ht
  have hH : y/eisensteinRowQuadratic c d (x,y) ≤
      9*(y/eisensteinRowQuadratic c d (t,y)) := by
    calc
      _ ≤ (9*y)/eisensteinRowQuadratic c d (t,y) :=
        (div_le_div_iff₀ hqx hqt).mpr (by nlinarith)
      _=_ := by ring
  have hpow := Real.rpow_le_rpow (div_nonneg hyp.le hqx.le) hH hs
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 9) (div_nonneg hyp.le hqt.le)] at hpow
  change ‖((y/eisensteinRowQuadratic c d (x,y):ℝ):ℂ)^s‖ ≤
    9^s.re*‖((y/eisensteinRowQuadratic c d (t,y):ℝ):ℂ)^s‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hyp hqx),
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hyp hqt)]
  exact hpow

end ArtinMatthews
