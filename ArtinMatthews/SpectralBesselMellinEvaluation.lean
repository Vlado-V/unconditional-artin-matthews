module

public import ArtinMatthews.SpectralSchlafliMellinMixture
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselMellinConvergence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Gamma-product Mellin multiplier of the actual arbitrary-order K. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralSchlafliMellinMixture_double_integral (ν s : ℂ)
    (hminus : ν.re < s.re) (hplus : -ν.re < s.re) :
    (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), spectralSchlafliMellinMixture ν s t x) =
      ((1/2 : ℂ)*(4 : ℂ)^((s-ν)/2)*Complex.Gamma ((s-ν)/2))*
        Complex.Gamma ((s+ν)/2) := by
  have hB : 0 < ((s+ν)/2).re := by simp only [Complex.div_ofNat_re,Complex.add_re]; linarith
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        ((1/2 : ℂ)*(4 : ℂ)^((s-ν)/2)*Complex.Gamma ((s-ν)/2))*
          ((t : ℂ)^((s+ν)/2-1)*Complex.exp (-(t : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact spectralSchlafliMellinMixture_integral_x ν s hminus ht
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

theorem schlafliBesselK_mellin_halves (ν s : ℂ)
    (hminus : ν.re < s.re) (hplus : -ν.re < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x) =
      (2 : ℂ)^(s-2)*Complex.Gamma ((s-ν)/2)*Complex.Gamma ((s+ν)/2) := by
  have hmix : Integrable (Function.uncurry (spectralSchlafliMellinMixture ν s))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    spectralSchlafliMellinMixture_integrable ν s hminus hplus
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4 : ℂ)^((s-ν)/2) = (2 : ℂ)^(2*((s-ν)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-ν)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2 : ℂ)^ν*(4 : ℂ)^((s-ν)/2) = (2 : ℂ)^s := by
    rw [h4,← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  have hscale : (1/4 : ℂ)*(2 : ℂ)^s = (2 : ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
    ring
  calc
    _ = ((1/2 : ℂ)*(2 : ℂ)^ν)*
        (∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), spectralSchlafliMellinMixture ν s t x) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_mellin_mixture ν s hx
    _ = ((1/2 : ℂ)*(2 : ℂ)^ν)*
        (((1/2 : ℂ)*(4 : ℂ)^((s-ν)/2)*Complex.Gamma ((s-ν)/2))*
          Complex.Gamma ((s+ν)/2)) := by
      rw [hswap,spectralSchlafliMellinMixture_double_integral ν s hminus hplus]
    _ = ((1/4 : ℂ)*((2 : ℂ)^ν*(4 : ℂ)^((s-ν)/2)))*
        Complex.Gamma ((s-ν)/2)*Complex.Gamma ((s+ν)/2) := by ring
    _ = _ := by rw [hprod,hscale]

theorem schlafliBesselK_mellin (ν s : ℂ) (hs : |ν.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x) =
      (2 : ℂ)^(s-2)*Complex.Gamma ((s-ν)/2)*Complex.Gamma ((s+ν)/2) :=
  schlafliBesselK_mellin_halves ν s
    (lt_of_le_of_lt (le_abs_self _) hs) (lt_of_le_of_lt (neg_le_abs _) hs)

theorem schlafliBesselK_scaled_mellin_integrable (ν s : ℂ) {q : ℝ}
    (hs : |ν.re| < s.re) (hq : 0 < q) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*schlafliBesselK ν (q*x)) (Ioi 0) := by
  have hb : MellinConvergent (schlafliBesselK ν) s := by
    simpa only [MellinConvergent,smul_eq_mul] using schlafliBesselK_mellin_integrable ν s hs
  have hh := (MellinConvergent.comp_mul_left (f := schlafliBesselK ν) (s := s) hq).mpr hb
  simpa only [MellinConvergent,smul_eq_mul] using hh

theorem schlafliBesselK_scaled_mellin (ν s : ℂ) {q : ℝ}
    (hs : |ν.re| < s.re) (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν (q*x)) =
      (q : ℂ)^(-s)*((2 : ℂ)^(s-2)*Complex.Gamma ((s-ν)/2)*Complex.Gamma ((s+ν)/2)) := by
  have hh := mellin_comp_mul_left (schlafliBesselK ν) s hq
  simp only [mellin,smul_eq_mul] at hh
  rw [schlafliBesselK_mellin ν s hs] at hh
  exact hh

end ArtinMatthews
