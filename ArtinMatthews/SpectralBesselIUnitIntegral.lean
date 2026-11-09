module

public import ArtinMatthews.SpectralUnitBeta


set_option backward.privateInPublic true
@[expose] public section

/-! Affine transport of the actual I Poisson integral to the unit interval.
Multiplication by exp(-x) exposes a positive Laplace parameter 2xt. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralBesselI_unit_poisson_point (ν : ℂ) (x t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Complex.exp ((-x*(2*t-1) : ℝ) : ℂ)*(1-((2*t-1 : ℝ) : ℂ)^2)^(ν-1/2) =
      Complex.exp (x : ℂ)*(4 : ℂ)^(ν-1/2)*
        (Complex.exp ((-2*x*t : ℝ) : ℂ)*spectralUnitBetaProfile (ν+1/2) (ν+1/2) t) := by
  have hpoly : 1-((2*t-1 : ℝ) : ℂ)^2 = ((4*(t*(1-t)) : ℝ) : ℂ) := by
    push_cast
    ring
  have he : ((-x*(2*t-1) : ℝ) : ℂ) = (x : ℂ)+((-2*x*t : ℝ) : ℂ) := by
    push_cast
    ring
  have hp := Complex.mul_cpow_ofReal_nonneg (a := (4 : ℝ)) (b := t*(1-t))
    (by norm_num) (mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)) (ν-1/2)
  rw [← Complex.ofReal_mul] at hp
  have hp2 := Complex.mul_cpow_ofReal_nonneg ht.1.le (sub_nonneg.mpr ht.2.le) (ν-1/2)
  rw [← Complex.ofReal_mul] at hp2
  rw [hpoly,hp,hp2,he,Complex.exp_add]
  unfold spectralUnitBetaProfile
  push_cast
  have hexp : ν+(1/2 : ℂ)-1 = ν-1/2 := by ring
  rw [hexp]
  ring

theorem spectralBesselI_unit_poisson (ν : ℂ) {x : ℝ} (hx : 0 < x)
    (hν : -(1/2 : ℝ) < ν.re) :
    spectralBesselI ν x =
      ((x/2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2)))*
      (2*Complex.exp (x : ℂ)*(4 : ℂ)^(ν-1/2))*
      ∫ t in Ioo (0 : ℝ) 1,
        Complex.exp ((-2*x*t : ℝ) : ℂ)*spectralUnitBetaProfile (ν+1/2) (ν+1/2) t := by
  rw [spectralBesselI_poisson ν hx hν]
  have hsub := intervalIntegral.smul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2))
    (2 : ℝ) (-1)
  norm_num only [mul_zero,zero_add,mul_one,add_neg_cancel_right] at hsub
  rw [← hsub,Complex.real_smul,intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  have hi : (∫ t in Ioo (0 : ℝ) 1,
      Complex.exp ((-x*(2*t-1) : ℝ) : ℂ)*(1-((2*t-1 : ℝ) : ℂ)^2)^(ν-1/2)) =
      (Complex.exp (x : ℂ)*(4 : ℂ)^(ν-1/2))*
        ∫ t in Ioo (0 : ℝ) 1,
          Complex.exp ((-2*x*t : ℝ) : ℂ)*spectralUnitBetaProfile (ν+1/2) (ν+1/2) t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact spectralBesselI_unit_poisson_point ν x t ht
  simp only [← sub_eq_add_neg]
  rw [hi]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem spectralBesselI_unit_coefficient (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    (x/2 : ℂ)^ν*2*(4 : ℂ)^(ν-1/2) = (2 : ℂ)^ν*(x : ℂ)^ν := by
  have hc := Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : (0 : ℝ) ≤ 2) ν
  have h4 := Complex.natCast_cpow_natCast_mul 2 2 (ν-(1/2 : ℂ))
  norm_num only [Nat.cast_ofNat,Nat.reducePow] at h4
  norm_num only [Complex.ofReal_ofNat] at hc
  rw [hc,← h4]
  have h2 : (2 : ℂ)^ν ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    exact Complex.exp_ne_zero _
  have hp : (2 : ℂ)^(2*(ν-1/2))*2 = (2 : ℂ)^(2*ν) := by
    calc
      _ = (2 : ℂ)^(2*(ν-1/2))*(2 : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ (by norm_num)]
        congr 1
        ring
  calc
    _ = (x : ℂ)^ν/(2 : ℂ)^ν*((2 : ℂ)^(2*(ν-1/2))*2) := by ring
    _ = _ := by
      rw [hp,Complex.cpow_ofNat_mul]
      field_simp [h2]

theorem spectralBesselI_damped_unit_integral (ν : ℂ) {x : ℝ} (hx : 0 < x)
    (hν : -(1/2 : ℝ) < ν.re) :
    Complex.exp (-(x : ℂ))*spectralBesselI ν x =
      ((2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2)))*(x : ℂ)^ν*
      ∫ t in Ioo (0 : ℝ) 1,
        Complex.exp ((-2*x*t : ℝ) : ℂ)*spectralUnitBetaProfile (ν+1/2) (ν+1/2) t := by
  rw [spectralBesselI_unit_poisson ν hx hν]
  have he : Complex.exp (-(x : ℂ))*Complex.exp (x : ℂ) = 1 := by
    rw [← Complex.exp_add,neg_add_cancel,Complex.exp_zero]
  calc
    _ = ((x/2 : ℂ)^ν*2*(4 : ℂ)^(ν-1/2))/
        ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))*
        (Complex.exp (-(x : ℂ))*Complex.exp (x : ℂ))*
        ∫ t in Ioo (0 : ℝ) 1,
          Complex.exp ((-2*x*t : ℝ) : ℂ)*spectralUnitBetaProfile (ν+1/2) (ν+1/2) t := by ring
    _ = _ := by rw [he,spectralBesselI_unit_coefficient ν hx]; ring

end ArtinMatthews
