module

public import ArtinMatthews.SpectralBesselMellinEvaluation
public import ArtinMatthews.SpectralGammaVerticalIntegrable
public import ArtinMatthews.SpectralBesselKEquation
public import Mathlib.Analysis.MellinInversion


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Mellin inversion for Schläfli K, using a proved integrable
Gamma-product multiplier on the full vertical line. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKMellinMultiplier (ν s : ℂ) : ℂ :=
  (2 : ℂ)^(s-2)*Complex.Gamma ((s-ν)/2)*Complex.Gamma ((s+ν)/2)

theorem spectral_Gamma_affine_vertical_integrable (a b d : ℝ) (ha : 0 < a) (hd : d ≠ 0) :
    Integrable (fun t : ℝ => Complex.Gamma ((a : ℂ)+((d*t+b : ℝ) : ℂ)*Complex.I)) := by
  exact ((spectral_Gamma_vertical_integrable a ha).comp_add_right b).comp_mul_left' hd

theorem spectralKMellinMultiplier_vertical_integrable (ν : ℂ) (σ : ℝ) (hσ : |ν.re| < σ) :
    Complex.VerticalIntegrable (spectralKMellinMultiplier ν) σ := by
  let a := (σ-ν.re)/2
  let b := (σ+ν.re)/2
  have ha : 0 < a := by dsimp [a]; linarith [le_abs_self ν.re]
  have hb : 0 < b := by dsimp [b]; linarith [neg_le_abs ν.re]
  have he1 (t : ℝ) : (((σ : ℂ)+(t : ℂ)*Complex.I)-ν)/2 =
      (a : ℂ)+((t/2-ν.im/2 : ℝ) : ℂ)*Complex.I := by
    dsimp [a]
    apply Complex.ext <;> simp
    ring
  have he2 (t : ℝ) : (((σ : ℂ)+(t : ℂ)*Complex.I)+ν)/2 =
      (b : ℂ)+((t/2+ν.im/2 : ℝ) : ℂ)*Complex.I := by
    dsimp [b]
    apply Complex.ext <;> simp
    ring
  have hG : Integrable (fun t : ℝ => Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)-ν)/2)) := by
    have h := spectral_Gamma_affine_vertical_integrable a (-ν.im/2) (1/2) ha (by norm_num)
    convert h using 1
    ext t
    rw [he1]
    congr 2
    ring
  have hcont : Continuous (fun t : ℝ => spectralKMellinMultiplier ν ((σ : ℂ)+(t : ℂ)*Complex.I)) := by
    have h1 : Continuous (fun t : ℝ => Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)-ν)/2)) := by
      simp_rw [he1]
      exact (spectral_Gamma_vertical_continuous a ha).comp (by fun_prop)
    have h2 : Continuous (fun t : ℝ => Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)+ν)/2)) := by
      simp_rw [he2]
      exact (spectral_Gamma_vertical_continuous b hb).comp (by fun_prop)
    exact ((show Continuous (fun t : ℝ => (2 : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-2)) by
      fun_prop).mul h1).mul h2
  let C := (2 : ℝ)^(σ-2)*Real.Gamma b
  have hC : 0 ≤ (2 : ℝ)^(σ-2) := Real.rpow_nonneg (by norm_num) _
  change Integrable (fun t : ℝ => spectralKMellinMultiplier ν ((σ : ℂ)+(t : ℂ)*Complex.I))
  apply (hG.norm.const_mul C).mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hg := spectral_Gamma_norm_le_real ((((σ : ℂ)+(t : ℂ)*Complex.I)+ν)/2) (by
    rw [he2]
    simpa using hb)
  have hp : ‖(2 : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-2)‖ = (2 : ℝ)^(σ-2) := by
    change ‖((2 : ℝ) : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-2)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0 < (2 : ℝ))]
    congr 1
    simp
  have hb' : (((σ : ℂ)+(t : ℂ)*Complex.I)+ν).re/2 = b := by dsimp [b]; simp
  have hg' : ‖Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)+ν)/2)‖ ≤ Real.Gamma b := by
    simpa only [Complex.div_ofNat_re,hb'] using hg
  unfold spectralKMellinMultiplier
  rw [norm_mul,norm_mul,hp]
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hg'
    (mul_nonneg hC (norm_nonneg (Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)-ν)/2))))]

theorem schlafliBesselK_mellin_vertical (ν : ℂ) (σ : ℝ) (hσ : |ν.re| < σ) :
    Complex.VerticalIntegrable (mellin (schlafliBesselK ν)) σ := by
  apply (spectralKMellinMultiplier_vertical_integrable ν σ hσ).congr
  filter_upwards [] with t
  unfold mellin
  simp only [smul_eq_mul]
  exact (schlafliBesselK_mellin ν ((σ : ℂ)+(t : ℂ)*Complex.I) (by simpa using hσ)).symm

theorem schlafliBesselK_mellin_inversion (ν : ℂ) (σ : ℝ) (hσ : |ν.re| < σ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (spectralKMellinMultiplier ν) x = schlafliBesselK ν x := by
  have hconv : MellinConvergent (schlafliBesselK ν) σ := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_re] using
      schlafliBesselK_mellin_integrable ν (σ : ℂ) hσ
  have h := mellinInv_mellin_eq σ (schlafliBesselK ν) hx hconv
    (schlafliBesselK_mellin_vertical ν σ hσ) (schlafliBesselK_hasDerivAt ν x hx).continuousAt
  rw [← h]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold mellin spectralKMellinMultiplier
  simp only [smul_eq_mul]
  exact (schlafliBesselK_mellin ν ((σ : ℂ)+(t : ℂ)*Complex.I) (by simpa using hσ)).symm

end ArtinMatthews
