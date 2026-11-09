module

public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralBesselKIConnection
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectral_integral_positive_pair (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ t : ℝ, F t) = ∫ t in Ioi (0 : ℝ), F t + F (-t) := by
  rw [integral_positive_negative_pair F hF]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact add_comm _ _

theorem spectralKLInverseIIntegrand_pair (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (heven : ∀ z : ℂ, h (-z) = h z)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    spectralKLInverseIIntegrand h g x (t : ℂ) + spectralKLInverseIIntegrand h g x (-t : ℂ) =
      ((Real.pi : ℂ) * Complex.I) *
        (schlafliBesselK ((t : ℂ) * Complex.I) x * spectralKLWindowData h g t *
          (spectralKLPlancherelWeight t : ℂ)) := by
  have hK := spectralKLCompactOrderTransform_even g hp ((t : ℂ) * Complex.I)
  have harg : Complex.I * (-(t : ℂ)) = -((t : ℂ) * Complex.I) := by ring
  have harg' : -Complex.I * (-(t : ℂ)) = (t : ℂ) * Complex.I := by ring
  have harg'' : -Complex.I * (t : ℂ) = -((t : ℂ) * Complex.I) := by ring
  have hs : Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) =
      ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.sin_mul_I, Complex.ofReal_sinh]
  have hconn := schlafliBesselK_eq_I_difference
    (ν := (t : ℂ) * Complex.I) (by simp) hx
  have hdiff : spectralBesselI (-((t : ℂ) * Complex.I)) x -
      spectralBesselI ((t : ℂ) * Complex.I) x =
        (2 / (Real.pi : ℂ)) * ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I *
          schlafliBesselK ((t : ℂ) * Complex.I) x := by
    rw [hs] at hconn
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    apply (mul_left_cancel₀ (show (Real.pi : ℂ) / 2 ≠ 0 by exact div_ne_zero hpi (by norm_num)))
    calc
      _ = ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I *
          schlafliBesselK ((t : ℂ) * Complex.I) x := hconn.symm
      _ = _ := by field_simp
  unfold spectralKLInverseIIntegrand
  rw [harg, harg', harg'', heven, hK, mul_comm Complex.I (t : ℂ)]
  calc
    _ = (t : ℂ) * h (t : ℂ) * spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I) *
        (spectralBesselI (-((t : ℂ) * Complex.I)) x - spectralBesselI ((t : ℂ) * Complex.I) x) := by ring
    _ = _ := by
      rw [hdiff]
      unfold spectralKLWindowData spectralKLPlancherelWeight
      push_cast
      field_simp

end
end ArtinMatthews
