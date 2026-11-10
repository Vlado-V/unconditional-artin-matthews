module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselJPoissonOrderDerivative
public import ArtinMatthews.SpectralGammaStripBound
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

theorem spectral_besselJ_poisson_norm_gamma_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : ℂ) (X : ℝ), 0 ≤ ν.re → 0 < X →
      ‖Complex.besselJ ν (X : ℂ)‖ ≤ C * X^ν.re * ‖(Complex.Gamma (ν+1/2))⁻¹‖ := by
  let w : ℝ → ℝ := fun u => spectralBesselJPoissonBase u^(-(1/2 : ℝ))
  let W := ∫ u in Ioo (-1 : ℝ) 1, w u
  have hW : 0 ≤ W := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Real.rpow_nonneg (spectralBesselJPoissonBase_pos hu).le _
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨(W+1)/Real.sqrt Real.pi,by positivity,?_⟩
  intro ν X hν hX
  have hMass : ‖spectralBesselJPoissonIntegral X ν‖ ≤ W := by
    unfold spectralBesselJPoissonIntegral
    apply norm_integral_le_of_norm_le
      (spectralBesselJPoissonRealWeight_integrable (a:=-(1/2 : ℝ)) (by norm_num))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hre : (ν-1/2).re = ν.re-1/2 := by norm_num
    rw [spectralBesselJPoissonIntegrand,norm_mul,spectral_besselJ_poisson_phase_norm,one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (spectralBesselJPoissonBase_pos hu),hre]
    exact Real.rpow_le_rpow_of_exponent_ge (spectralBesselJPoissonBase_pos hu)
      (spectralBesselJPoissonBase_le_one u) (by linarith)
  have hpref : ‖((X : ℂ)/2)^ν‖ = (X/2)^ν.re := by
    rw [show ((X : ℂ)/2) = ((X/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hX)]
  have hpow : (X/2)^ν.re ≤ X^ν.re :=
    Real.rpow_le_rpow (by positivity) (by linarith) hν
  rw [spectral_besselJ_poisson_setIntegral X (by linarith)]
  calc
    _ = ((X/2)^ν.re * ‖(Complex.Gamma (ν+1/2))⁻¹‖) *
        (‖spectralBesselJPoissonIntegral X ν‖/Real.sqrt Real.pi) := by
      rw [norm_mul,norm_div,norm_mul,hpref,Complex.norm_real,Real.norm_of_nonneg hπ.le,norm_inv]
      ring
    _ ≤ (X^ν.re * ‖(Complex.Gamma (ν+1/2))⁻¹‖) * ((W+1)/Real.sqrt Real.pi) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      · exact div_le_div_of_nonneg_right (hMass.trans (by linarith)) hπ.le
      · positivity
      · positivity
    _ = _ := by ring

theorem spectral_besselJ_vertical_allX (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t X : ℝ), 0 < X →
      ‖Complex.besselJ ((c : ℂ)+2*(t : ℂ)*I) (X : ℂ)‖ ≤
        C*Real.exp (Real.pi*|t|)*X^c := by
  obtain ⟨D,hD,hp⟩ := spectral_besselJ_poisson_norm_gamma_inv
  obtain ⟨G,hG,hg⟩ := spectral_inv_gamma_vertical_bound c hc
  refine ⟨D*G,mul_pos hD hG,?_⟩
  intro t X hX
  let ν : ℂ := (c : ℂ)+2*(t : ℂ)*I
  have hre : ν.re = c := by norm_num [ν,Complex.mul_re,Complex.mul_im]
  have harg : ν+1/2 = ((c+1/2 : ℝ) : ℂ)+2*(t : ℂ)*I := by
    dsimp [ν]
    push_cast
    ring
  have h := hp ν X (by rwa [hre]) hX
  rw [hre,harg] at h
  calc
    _ ≤ D*X^c*‖(Complex.Gamma (((c+1/2 : ℝ) : ℂ)+2*(t : ℂ)*I))⁻¹‖ := h
    _ ≤ D*X^c*(G*Real.exp (Real.pi*|t|)) := mul_le_mul_of_nonneg_left (hg t) (by positivity)
    _ = _ := by ring

theorem spectral_besselJ_closed_strip_allX (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c t X : ℝ), 0 ≤ c → c ≤ B → 0 < X →
      ‖Complex.besselJ ((c : ℂ)+2*(t : ℂ)*I) (X : ℂ)‖ ≤
        C*(1+|t|)*Real.exp (Real.pi*|t|)*X^c := by
  obtain ⟨D,hD,hp⟩ := spectral_besselJ_poisson_norm_gamma_inv
  obtain ⟨G,hG,hg⟩ := spectral_inv_gamma_closed_strip_bound B hB
  refine ⟨2*D*G,by positivity,?_⟩
  intro c t X hc hcB hX
  let ν : ℂ := (c : ℂ)+2*(t : ℂ)*I
  have hre : ν.re = c := by norm_num [ν,Complex.mul_re,Complex.mul_im]
  have harg : ν+1/2 = ((c+1/2 : ℝ) : ℂ)+((2*t : ℝ) : ℂ)*I := by
    dsimp [ν]
    push_cast
    ring
  have h := hp ν X (by rwa [hre]) hX
  rw [hre,harg] at h
  have hΓ := hg c (2*t) hc hcB
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2),
    show Real.pi*(2*|t|)/2 = Real.pi*|t| by ring] at hΓ
  calc
    _ ≤ D*X^c*‖(Complex.Gamma (((c+1/2 : ℝ) : ℂ)+((2*t : ℝ) : ℂ)*I))⁻¹‖ := h
    _ ≤ D*X^c*(G*(1+2*|t|)*Real.exp (Real.pi*|t|)) :=
      mul_le_mul_of_nonneg_left hΓ (by positivity)
    _ ≤ D*X^c*(G*(2*(1+|t|))*Real.exp (Real.pi*|t|)) := by gcongr; linarith
    _ = _ := by ring

end
end ArtinMatthews
