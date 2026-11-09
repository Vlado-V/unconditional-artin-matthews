module

public import ArtinMatthews.SpectralWeylRadialGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! Dimensionless Weyl kernel and its evaluated Gaussian modulus transform.
The two real phase signs stay separate until a sign sector is selected. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralWeylDimensionlessKernel (s t X x z : ℝ) : ℝ :=
  spectralWeylRadialKernel (4*x*z) ((s*x+t*z)/(2*Real.sqrt (x*z))) X

theorem spectralWeylDimensionlessKernel_eq {x z X : ℝ} (hx : 0 < x) (hz : 0 < z)
    (hX : 2*Real.sqrt (x*z) < X) (s t : ℝ) :
    spectralWeylDimensionlessKernel s t X x z =
      Real.cos ((s*x+t*z)*Real.sqrt (X^2/(4*x*z)-1))/Real.sqrt (X^2/4-x*z) := by
  have hxz : 0 < x*z := mul_pos hx hz
  have hA : 0 < 4*x*z := by positivity
  have hsA : Real.sqrt (4*x*z) = 2*Real.sqrt (x*z) := by
    rw [show 4*x*z = 4*(x*z) by ring,Real.sqrt_mul (by norm_num)]
    norm_num
  have hX0 : 0 < X := (mul_pos two_pos (Real.sqrt_pos.mpr hxz)).trans hX
  have hr : 0 < X^2-4*x*z := by
    have hh := mul_pos (sub_pos.mpr hX)
      (add_pos hX0 (mul_pos two_pos (Real.sqrt_pos.mpr hxz)))
    nlinarith [Real.sq_sqrt hxz.le]
  have hden : Real.sqrt (X^2/4-x*z) = Real.sqrt (X^2-4*x*z)/2 := by
    rw [show X^2/4-x*z = (X^2-4*x*z)/4 by ring,Real.sqrt_div hr.le]
    norm_num
  have hphase : Real.sqrt (X^2/(4*x*z)-1) = Real.sqrt (X^2-4*x*z)/(2*Real.sqrt (x*z)) := by
    rw [show X^2/(4*x*z)-1 = (X^2-4*x*z)/(4*x*z) by field_simp,Real.sqrt_div hr.le,hsA]
  unfold spectralWeylDimensionlessKernel spectralWeylRadialKernel
  rw [ite_eq_left (hsA ▸ hX),hden,hphase]
  have he : ((s*x+t*z)/(2*Real.sqrt (x*z)))*Real.sqrt (X^2-4*x*z) =
      (s*x+t*z)*(Real.sqrt (X^2-4*x*z)/(2*Real.sqrt (x*z))) := by ring
  rw [he]
  ring

theorem spectralWeylDimensionlessKernel_gaussian_integrable {x z p : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hp : 0 < p) (s t : ℝ) :
    Integrable (fun X : ℝ => Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z) :=
  spectralWeylRadialGaussian_integrable (by positivity) hp _

theorem spectralWeylDimensionlessKernel_gaussian {x z p : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hp : 0 < p) (s t : ℝ) :
    (∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z) =
      Real.sqrt (Real.pi/p)*Real.exp (-4*p*x*z-(s*x+t*z)^2/(16*p*x*z)) := by
  have h := spectralWeylRadialGaussian_integral (A := 4*x*z) (by positivity) hp
    ((s*x+t*z)/(2*Real.sqrt (x*z)))
  change (∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z) = _ at h
  rw [h]
  congr 2
  rw [div_pow,mul_pow,Real.sq_sqrt (mul_pos hx hz).le]
  field_simp
  ring

theorem spectralWeylDimensionlessKernel_gaussian_signs {x z p : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hp : 0 < p) (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    (∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z) =
      Real.sqrt (Real.pi/p)*Real.exp (-4*p*x*z-(x/z+z/x+2*s*t)/(16*p)) := by
  rw [spectralWeylDimensionlessKernel_gaussian hx hz hp]
  congr 2
  field_simp
  nlinarith [hs,ht]

end ArtinMatthews
