module

public import ArtinMatthews.SpectralGaussianJSeries
public import ArtinMatthews.SpectralBesselIUnitIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Gaussian J evaluation from its absolutely integrated series
and the actual I Poisson integral. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace ArtinMatthews

theorem spectralGaussianJ_I_power (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (q/2 : ℂ)^(2*ν) = (2 : ℂ)^ν*(((q^2/8 : ℝ) : ℂ)^ν) := by
  have hh : 0 < q/2 := half_pos hq
  have hv : 0 < q^2/8 := div_pos (sq_pos_of_pos hq) (by norm_num)
  have hbase : (q/2 : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have h2 := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := q^2/8) (by norm_num) hv.le ν
  have hq2 := Complex.mul_cpow_ofReal_nonneg hh.le hh.le ν
  rw [← Complex.ofReal_mul] at h2 hq2
  norm_num only [Complex.ofReal_ofNat,Complex.ofReal_div] at h2 hq2
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [← h2,show (2 : ℝ)*(q^2/8) = (q/2)*(q/2) by ring,hq2,
    show 2*ν = ν+ν by ring,Complex.cpow_add _ _ hbase]

theorem spectralGaussianJ_evaluation (ν : ℂ) (hν : -(1/2 : ℝ) < ν.re)
    {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(x : ℂ)^2)*Complex.besselJ (2*ν) ((q : ℂ)*(x : ℂ))) =
      ((Real.sqrt Real.pi : ℂ)/2)*Complex.exp (-((q^2/8 : ℝ) : ℂ))*spectralBesselI ν (q^2/8) := by
  let a : ℂ := ν+1/2
  let z : ℂ := -(q/2 : ℂ)^2
  let v : ℝ := q^2/8
  have ha : 0 < a.re := by dsimp [a]; norm_num; linarith
  have hv : 0 < v := div_pos (sq_pos_of_pos hq) (by norm_num)
  have hsum := (spectralBeta_exponential_gamma_hasSum a a z ha ha).tsum_eq
  have hg : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have hroot : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hi : (∫ t : ℝ in (0 : ℝ)..1, Complex.exp (z*t)*spectralUnitBetaProfile a a t) =
      ∫ t in Ioo (0 : ℝ) 1, Complex.exp ((-2*v*t : ℝ) : ℂ)*spectralUnitBetaProfile a a t := by
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t _
    dsimp only
    congr 1
    congr 1
    dsimp [z,v]
    push_cast
    ring
  have hden (n : ℕ) : a+a+(n : ℂ) = 2*ν+1+n := by dsimp [a]; ring
  simp_rw [hden] at hsum
  rw [hi] at hsum
  rw [spectralGaussianJ_gamma_integral ν hν hq]
  change (q/2 : ℂ)^(2*ν)*(1/2 : ℂ)*
    (∑' n : ℕ, Complex.Gamma (a+n)*z^n/((n.factorial : ℂ)*Complex.Gamma (2*ν+1+n))) = _
  rw [hsum]
  have hI := spectralBesselI_damped_unit_integral ν hv hν
  change Complex.exp (-(v : ℂ))*spectralBesselI ν v = _ at hI
  change _ = ((Real.sqrt Real.pi : ℂ)/2)*Complex.exp (-(v : ℂ))*spectralBesselI ν v
  rw [mul_assoc ((Real.sqrt Real.pi : ℂ)/2) (Complex.exp (-(v : ℂ))) (spectralBesselI ν v),
    hI,spectralGaussianJ_I_power ν hq]
  change _ = ((Real.sqrt Real.pi : ℂ)/2)*
    (((2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma a))*(v : ℂ)^ν*
      ∫ t in Ioo (0 : ℝ) 1, Complex.exp ((-2*v*t : ℝ) : ℂ)*spectralUnitBetaProfile a a t)
  field_simp [hroot,hg]
  dsimp only [v]
  ring_nf

end ArtinMatthews
