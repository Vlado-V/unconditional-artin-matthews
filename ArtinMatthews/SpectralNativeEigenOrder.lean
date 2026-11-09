module

public import ArtinMatthews.SpectralNativeHeightProfile
public import Mathlib.Analysis.RCLike.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Every nonnegative ambient eigenvalue lies in the closed order strip
needed by the genuine inverse-profile transform, including eigenvalue zero. -/

noncomputable section
namespace ArtinMatthews

theorem spectralNonnegativeEnergy_order_abs_re_le (eig : ℝ) (heig : 0 ≤ eig) :
    |(Complex.sqrt (1/4-(eig : ℂ))).re| ≤ 1/2 := by
  have he : (1/4-(eig : ℂ)) = ((1/4-eig : ℝ) : ℂ) := by norm_num
  rw [he,Complex.re_sqrt_ofReal,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith⟩

end ArtinMatthews
