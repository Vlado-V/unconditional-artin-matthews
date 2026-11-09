module

public import ArtinMatthews.SpectralKLMacdonaldAnalysis
public import ArtinMatthews.SpectralWeylGaussianKAction


set_option backward.privateInPublic true
@[expose] public section

/-! Completed KL analysis of the actual Gaussian-in-modulus Weyl
profile.  The geometric integral is literal and its integration order is
kept; all noncompact L2 and K0-majorant conditions are discharged. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKLWeylGaussianProfile (s t x p z : ℝ) : ℂ :=
  if 0 < z then
    ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)
  else 0

def spectralKLWeylGaussianConstant (s t p : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((-(s*t)/(8*p) : ℝ) : ℂ)

theorem spectralKLWeylGaussianProfile_factor {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (z : ℝ) :
    spectralKLWeylGaussianProfile s t x p z =
      spectralKLWeylGaussianConstant s t p*spectralKLMacdonaldProfile x (1/(8*p)) z := by
  by_cases hz : 0 < z
  · rw [spectralKLWeylGaussianProfile,ite_eq_left hz,
      spectralWeylDimensionlessKernel_gaussian_signs hx hz hp s t hs ht]
    unfold spectralKLWeylGaussianConstant spectralKLMacdonaldProfile spectralKLExpReciprocal
    rw [ite_eq_left hz,Complex.ofReal_mul,Complex.ofReal_exp]
    have he : ((-4*p*x*z-(x/z+z/x+2*s*t)/(16*p) : ℝ) : ℂ) =
        ((-(s*t)/(8*p) : ℝ) : ℂ)+
          (-((((x^2+(1/(8*p))^2)/(2*x*(1/(8*p))) : ℝ) : ℂ))*(z : ℂ)-
            (((x*(1/(8*p))/2 : ℝ) : ℂ))/(z : ℂ)) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hp.ne',Complex.ofReal_ne_zero.mpr hx.ne',
        Complex.ofReal_ne_zero.mpr hz.ne']
      ring
    rw [he,Complex.exp_add]
    ring
  · simp only [spectralKLWeylGaussianProfile,ite_eq_right hz,
      spectralKLMacdonaldProfile_nonpositive_zero x (1/(8*p)) z (le_of_not_gt hz),mul_zero]

theorem spectralKLWeylGaussianProfile_memLp {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    MemLp (spectralKLWeylGaussianProfile s t x p) 2 spectralKLPhysicalMeasure := by
  have hy : 0 < 1/(8*p) := one_div_pos.mpr (by positivity)
  have h := (spectralKLMacdonaldProfile_memLp hx hy).const_smul (spectralKLWeylGaussianConstant s t p)
  apply (memLp_congr_ae (Filter.Eventually.of_forall (spectralKLWeylGaussianProfile_factor hx hp s t hs ht))).mpr
  simpa only [smul_eq_mul] using! h

theorem spectralKLWeylGaussianProfile_measurable {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    Measurable (spectralKLWeylGaussianProfile s t x p) := by
  have he : spectralKLWeylGaussianProfile s t x p =
      fun z => spectralKLWeylGaussianConstant s t p*spectralKLMacdonaldProfile x (1/(8*p)) z :=
    funext (spectralKLWeylGaussianProfile_factor hx hp s t hs ht)
  rw [he]
  exact (spectralKLMacdonaldProfile_measurable x (1/(8*p))).const_mul _

theorem spectralKLWeylGaussianProfile_nonpositive_zero (s t x p z : ℝ) (hz : z ≤ 0) :
    spectralKLWeylGaussianProfile s t x p z = 0 := by
  simp only [spectralKLWeylGaussianProfile,ite_eq_right (not_lt.mpr hz)]

theorem spectralKLWeylGaussianProfile_majorant_integrable {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    Integrable (spectralKLIntegrableMajorant (spectralKLWeylGaussianProfile s t x p)) := by
  have hy : 0 < 1/(8*p) := one_div_pos.mpr (by positivity)
  have h := (spectralKLMacdonaldProfile_majorant_integrable hx hy).const_mul
    ‖spectralKLWeylGaussianConstant s t p‖
  apply h.congr
  filter_upwards with z
  unfold spectralKLIntegrableMajorant spectralKLPhysicalCompactDiv
  rw [spectralKLWeylGaussianProfile_factor hx hp s t hs ht,mul_div_assoc,norm_mul]
  ring

theorem spectralKLWeylGaussianProfile_literal_analysis {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (r : ℝ) :
    spectralKLPhysicalAnalysisIntegral (spectralKLWeylGaussianProfile s t x p) r =
      2*spectralKLWeylGaussianConstant s t p*schlafliBesselK ((r : ℂ)*Complex.I) x*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  rw [spectralKLAnalysis_integral_of_nonpositive_zero _ (spectralKLWeylGaussianProfile_nonpositive_zero s t x p)]
  calc
    _ = ∫ z in Ioi (0 : ℝ),
        ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
          schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      change 0 < z at hz
      dsimp only
      rw [spectralKLWeylGaussianProfile,ite_eq_left hz]
      ring
    _ = _ := by
      rw [spectralWeylGaussian_K_action hx hp s t r hs ht]
      unfold spectralKLWeylGaussianConstant
      ring

theorem spectralKLWeylGaussianProfile_completed_analysis {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    spectralKLAnalysis ((spectralKLWeylGaussianProfile_memLp hx hp s t hs ht).toLp
      (spectralKLWeylGaussianProfile s t x p)) =ᵐ[spectralKLSpectralMeasure]
        (fun r : ℝ => 2*spectralKLWeylGaussianConstant s t p*schlafliBesselK ((r : ℂ)*Complex.I) x*
          schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p))) := by
  have h := spectralKLAnalysis_majorant_ae _ (spectralKLWeylGaussianProfile_measurable hx hp s t hs ht)
    (spectralKLWeylGaussianProfile_nonpositive_zero s t x p)
    (spectralKLWeylGaussianProfile_majorant_integrable hx hp s t hs ht)
    (spectralKLWeylGaussianProfile_memLp hx hp s t hs ht)
  exact h.trans (Filter.Eventually.of_forall (spectralKLWeylGaussianProfile_literal_analysis hx hp s t hs ht))

end ArtinMatthews
