module

public import ArtinMatthews.SpectralWeberKClosed
public import ArtinMatthews.SpectralWeberKScalar


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit Weber expression has the same actual Mellin transform
as the Gaussian K integral; every constant is evaluated here. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralWeberKClosed_mellin (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    mellin (spectralWeberKClosed ν) s =
      Complex.Gamma s*(2 : ℂ)^(-1-2*s)*Complex.Gamma (1/2-s-ν)*
        Complex.Gamma (1/2-s+ν) := by
  have hleft : |ν.re| < ((1/2 : ℂ)-s).re := by norm_num; linarith
  have hright : ((1/2 : ℂ)-s).re < 1/2 := by norm_num; linarith
  rw [spectralWeberKClosed_mellin_scale,
    (spectralAntiK_hasMellin ν (1/2-s) hleft hright).2,
    show ((1/2 : ℂ)-s)+1/2 = 1-s by ring]
  calc
    _ = (((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        (1/8 : ℂ)^(s-1/2)*
        ((Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-(1/2-s))*Complex.cos ((Real.pi : ℂ)*ν)/
          (Complex.Gamma (1-s)*Complex.cos ((Real.pi : ℂ)*(1/2-s)))))*
        Complex.Gamma (1/2-s-ν)*Complex.Gamma (1/2-s+ν) := by ring
    _ = _ := by rw [spectralWeberK_scalar ν s hs hstrip]

end ArtinMatthews
