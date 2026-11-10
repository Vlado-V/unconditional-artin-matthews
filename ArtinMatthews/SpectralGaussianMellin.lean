module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.SpectralLaplaceGamma
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Gaussian complex moments obtained by the actual positive-square
change of variables in Mellin integration. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralGaussianMellin_integrable (s : ℂ) {p : ℝ} (hs : 0 < s.re) (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*Complex.exp (-(p : ℂ)*(x : ℂ)^2))
      (Ioi (0 : ℝ)) := by
  have hh : 0 < (s/2).re := by simpa using half_pos hs
  have hc : MellinConvergent (fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul] using spectralLaplaceGamma_integrable (s/2) hh hp
  have h := (MellinConvergent.comp_rpow
    (f := fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ))) (s := s) (a := 2) (by norm_num)).mpr hc
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,Complex.ofReal_pow] using h

theorem spectralGaussianMellin_integral (s : ℂ) {p : ℝ} (hs : 0 < s.re) (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(p : ℂ)*(x : ℂ)^2)) =
      (1/2 : ℂ)*(1/(p : ℂ))^(s/2)*Complex.Gamma (s/2) := by
  have hh : 0 < (s/2).re := by simpa using half_pos hs
  have h := mellin_comp_rpow (fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ))) s 2
  have hl : mellin (fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ))) (s/2) =
      (1/(p : ℂ))^(s/2)*Complex.Gamma (s/2) := by
    simpa only [mellin,smul_eq_mul] using spectralLaplaceGamma_integral (s/2) hh hp
  norm_num only [Complex.ofReal_ofNat] at h
  rw [hl] at h
  simpa only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_pow,abs_of_pos (show 0 < (2 : ℝ) by norm_num),
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,mul_assoc] using! h

end ArtinMatthews
