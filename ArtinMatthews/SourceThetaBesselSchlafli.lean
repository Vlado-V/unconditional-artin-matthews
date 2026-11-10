module

public import ArtinMatthews.SourceThetaSchlafliMoments
public import ArtinMatthews.SourceThetaBesselMellin
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Exact equality of the source positive cubic Bessel factor and
the positive Schläfli moment. No asymptotic replacement is used. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter OAI.CubicEisenstein
noncomputable section

def sourceThetaBesselNormalizer (c : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (c / 2) ^ (-(1 / 3 : ℝ))

theorem sourceThetaBesselNormalizer_pos {c : ℝ} (hc : 0 < c) :
    0 < sourceThetaBesselNormalizer c := by
  unfold sourceThetaBesselNormalizer
  positivity

theorem sourceThetaBesselSchlafli_scale_pos {c : ℝ} (hc : 0 < c) : 0 < c ^ 2 / 4 := by
  positivity

private theorem thetaSqrtExp (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring_nf

private theorem thetaBessel_power_scale {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Real.exp x * ((1 / 2 : ℝ) * (c * Real.sqrt (Real.exp x) / 2) ^ (-(1 / 3 : ℝ))) =
      sourceThetaBesselNormalizer c * Real.exp ((5 / 6 : ℝ) * x) := by
  rw [show c * Real.sqrt (Real.exp x) / 2 = (c / 2) * Real.sqrt (Real.exp x) by ring_nf,
    Real.mul_rpow (by positivity : 0 ≤ c / 2) (Real.sqrt_nonneg _), thetaSqrtExp,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  calc
    _ = sourceThetaBesselNormalizer c * (Real.exp x * Real.exp ((x / 2) * (-(1 / 3 : ℝ)))) := by
      unfold sourceThetaBesselNormalizer
      ring_nf
    _ = _ := by rw [← Real.exp_add]; congr 2; ring_nf

private theorem thetaSchlafli_cubic_integral (c x : ℝ) :
    sourceThetaSchlafliMoment (c ^ 2 / 4) 0 x =
      Real.exp ((5 / 6 : ℝ) * x) *
        ∫ z in Ioi 0, cubicBesselDensity (c * Real.sqrt (Real.exp x)) z := by
  unfold sourceThetaSchlafliMoment
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  unfold sourceThetaSchlafliMomentIntegrand cubicBesselDensity sourceThetaSchlafliPhase
  rw [pow_zero, one_mul, mul_pow, Real.sq_sqrt (Real.exp_pos x).le]
  have he : c ^ 2 / 4 * Real.exp x / z = c ^ 2 * Real.exp x / (4 * z) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring_nf
  rw [he]
  simp only [neg_div]

theorem sourceThetaBesselProfile_exp_eq_moment {c : ℝ} (hc : 0 < c) (x : ℝ) :
    sourceThetaBesselProfile c (Real.exp x) =
      ((sourceThetaBesselNormalizer c * sourceThetaSchlafliMoment (c ^ 2 / 4) 0 x : ℝ) : ℂ) := by
  have hArg : 0 < c * Real.sqrt (Real.exp x) := mul_pos hc (Real.sqrt_pos.2 (Real.exp_pos _))
  rw [sourceThetaBesselProfile, schlafliBesselK_cubic_real _ hArg, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [thetaSchlafli_cubic_integral c x]
  calc
    _ = (Real.exp x * ((1 / 2 : ℝ) *
        (c * Real.sqrt (Real.exp x) / 2) ^ (-(1 / 3 : ℝ)))) *
        ∫ z in Ioi 0, cubicBesselDensity (c * Real.sqrt (Real.exp x)) z := by ring_nf
    _ = _ := by rw [thetaBessel_power_scale hc x]; ring_nf

theorem sourceThetaBesselProfile_pos {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    0 < (sourceThetaBesselProfile c T).re := by
  rw [← Real.exp_log hT, sourceThetaBesselProfile_exp_eq_moment hc, Complex.ofReal_re]
  exact mul_pos (sourceThetaBesselNormalizer_pos hc)
    (sourceThetaSchlafliMoment_pos (sourceThetaBesselSchlafli_scale_pos hc) 0 _)

end
end ArtinMatthews.SourceReflection
