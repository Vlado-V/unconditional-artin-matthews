module

public import ArtinMatthews.SpectralKLDirectIAnalytic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectralKLDirectIIntegrand_pair (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    spectralKLDirectIIntegrand F x (t : ℂ) + spectralKLDirectIIntegrand F x (-t : ℂ) =
      ((Real.pi : ℂ) * Complex.I) *
        (schlafliBesselK ((t : ℂ) * Complex.I) x * F (t : ℂ) *
          (spectralKLPlancherelWeight t : ℂ)) := by
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
  unfold spectralKLDirectIIntegrand
  rw [harg', harg'', heven]
  calc
    _ = (t : ℂ) * F (t : ℂ) *
        (spectralBesselI (-((t : ℂ) * Complex.I)) x - spectralBesselI ((t : ℂ) * Complex.I) x) := by ring
    _ = _ := by
      rw [hdiff]
      unfold spectralKLPlancherelWeight
      push_cast
      field_simp


end
end ArtinMatthews
