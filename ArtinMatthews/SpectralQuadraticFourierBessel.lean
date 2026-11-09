module

public import ArtinMatthews.SpectralQuadraticFourierReduction
public import ArtinMatthews.SpectralCuspFourierODEHorizontal


set_option backward.privateInPublic true
@[expose] public section

/-! The actual one-dimensional quadratic Fourier integral is evaluated
through the proved two-dimensional Schlaefli kernel and absolute Fubini. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralRealFourierPhase_int (n : ℤ) (x : ℝ) :
    spectralRealFourierPhase (n : ℝ) x = cuspFourierPhase 1 n x := by
  unfold spectralRealFourierPhase cuspFourierPhase cuspFourierFrequency
  congr 1
  push_cast
  ring

theorem spectralQuadraticFourier_bessel (s : ℂ) (hs : 1/2 < s.re) (b : ℝ) (hb : b ≠ 0) :
    spectralQuadraticFourier s b =
      ((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2) *
          schlafliBesselK (s-1/2) (2*Real.pi*|b|) := by
  have hS : 1 < (s+(1/2 : ℂ)).re := by
    simp only [Complex.add_re]
    norm_num
    linarith
  have hbC : (((b/2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast div_ne_zero hb (by norm_num : (2 : ℝ) ≠ 0)
  have hn : ‖((b/2 : ℝ) : ℂ)‖ = |b|/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have hKernel := sourceFourierKernel_bessel (s+1/2) ((b/2 : ℝ) : ℂ) hS hbC
  rw [hn,show s+(1/2 : ℂ)-1=s-1/2 by ring,
    show (2 : ℂ)*(Real.pi : ℂ)*((|b|/2 : ℝ) : ℂ) =
      ((Real.pi*|b| : ℝ) : ℂ) by push_cast;ring,
    show 4*Real.pi*(|b|/2)=2*Real.pi*|b| by ring] at hKernel
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hGS : Complex.Gamma (s+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hsq : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hroot : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  let C : ℂ := (Real.sqrt Real.pi : ℂ)*Complex.Gamma s/Complex.Gamma (s+1/2)
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero hroot hG) hGS
  have hScalar : C*((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) =
      (2*Real.pi : ℂ)/Complex.Gamma (s+1/2) := by
    dsimp only [C]
    calc
      _ = (2*(Real.sqrt Real.pi : ℂ)^2/Complex.Gamma (s+1/2)) *
          (Complex.Gamma s/Complex.Gamma s) := by ring
      _ = _ := by rw [div_self hG,mul_one,hsq]
  apply mul_left_cancel₀ hC
  calc
    C*spectralQuadraticFourier s b = sourceFourierKernel (s+1/2) ((b/2 : ℝ) : ℂ) :=
      spectralQuadraticFourier_dimensional_reduction s hs b
    _ = _ := hKernel
    _ = C*(((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)*schlafliBesselK (s-1/2) (2*Real.pi*|b|)) := by
      rw [show C*(((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
          ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)*schlafliBesselK (s-1/2) (2*Real.pi*|b|)) =
          (C*((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s)) *
            ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)*schlafliBesselK (s-1/2) (2*Real.pi*|b|) by ring,
        hScalar]

end ArtinMatthews

