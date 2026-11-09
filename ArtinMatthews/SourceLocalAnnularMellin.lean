module

public import ArtinMatthews.SourceLocalBallMellin
public import ArtinMatthews.StandardLocalUnitTest


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Mellin transform of the standard Fourier transform of the
finite unit annulus, on the actual multiplicative Haar. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K
local notation "q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "μ" => sourceLocalMulMeasure K P
local notation "c" => Measure.real (sourceLocalSelfDual K P) (sourceLocalBall K P 0)
local notation "d" => sourceDifferentExponent K P

def sourceLocalAnnularMellinIntegrand (z : ℂ) (u : kˣ) : ℂ :=
  sourceLocalFourier K P (sourceLocalUnitTest K P) (u : k) * sourceLocalMellinWeight K P z u

def sourceLocalAnnularMellin (z : ℂ) : ℂ :=
  ∫ u, sourceLocalAnnularMellinIntegrand K P z u ∂μ

theorem sourceLocalMellinWeight_indicator_ball (n : ℤ) (z : ℂ) (u : kˣ) :
    sourceLocalBallIndicator K P n (u : k) * sourceLocalMellinWeight K P z u =
      (sourceLocalMulBall K P n).indicator (sourceLocalMellinWeight K P z) u := by
  by_cases hu : (u : k) ∈ sourceLocalBall K P n <;>
    simp [sourceLocalBallIndicator, sourceLocalMulBall, hu]

theorem sourceLocalAnnularMellinIntegrand_eq (z : ℂ) (u : kˣ) :
    sourceLocalAnnularMellinIntegrand K P z u =
      (c : ℂ) * (sourceLocalMulBall K P (d : ℤ)).indicator (sourceLocalMellinWeight K P z) u -
      ((c / q : ℝ) : ℂ) *
        (sourceLocalMulBall K P ((d : ℤ) + 1)).indicator (sourceLocalMellinWeight K P z) u := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  rw [sourceLocalAnnularMellinIntegrand, sourceLocalUnitTestFourier_raw, sourceLocalPrimeBall_volume,
    sub_mul, mul_assoc, mul_assoc, sourceLocalMellinWeight_indicator_ball,
    sourceLocalMellinWeight_indicator_ball]

theorem sourceLocalMellinWeight_integrable_indicator (n : ℤ) (z : ℂ) (hz : 0 < z.re) :
    Integrable ((sourceLocalMulBall K P n).indicator (sourceLocalMellinWeight K P z)) μ :=
  (sourceLocalMellinWeight_integrable_ball K P n z hz).integrable_indicator
    (sourceLocalMulBall_measurable K P n)

theorem sourceLocalAnnularMellin_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (sourceLocalAnnularMellinIntegrand K P z) μ := by
  rw [funext (sourceLocalAnnularMellinIntegrand_eq K P z)]
  exact ((sourceLocalMellinWeight_integrable_indicator K P (d : ℤ) z hz).const_mul (c : ℂ)).sub
    ((sourceLocalMellinWeight_integrable_indicator K P ((d : ℤ) + 1) z hz).const_mul ((c / q : ℝ) : ℂ))

theorem sourceLocalAnnularMellin_eq (z : ℂ) (hz : 0 < z.re) :
    sourceLocalAnnularMellin K P z =
      (c : ℂ) * (sourceLocalMellinShellMass K P : ℂ) *
        (q : ℂ) ^ ((d : ℂ) * z) * (1 - (q : ℂ) ^ (z - 1)) / (1 - (q : ℂ) ^ (-z)) := by
  unfold sourceLocalAnnularMellin
  simp_rw [sourceLocalAnnularMellinIntegrand_eq]
  rw [integral_sub
    ((sourceLocalMellinWeight_integrable_indicator K P (d : ℤ) z hz).const_mul (c : ℂ))
    ((sourceLocalMellinWeight_integrable_indicator K P ((d : ℤ) + 1) z hz).const_mul ((c / q : ℝ) : ℂ)),
    integral_const_mul, integral_const_mul, integral_indicator (sourceLocalMulBall_measurable K P _),
    integral_indicator (sourceLocalMulBall_measurable K P _),
    sourceLocalMellinWeight_integral_ball K P _ z hz, sourceLocalMellinWeight_integral_ball K P _ z hz]
  have hq : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceLocalNorm_pos K P).ne'
  have he : (((d : ℤ) + 1 : ℤ) : ℂ) * z = (d : ℂ) * z + z := by push_cast; ring
  rw [he, Int.cast_natCast, Complex.cpow_add _ _ hq, Complex.cpow_sub _ _ hq, Complex.cpow_one,
    Complex.ofReal_div]
  ring

theorem sourceLocalAnnularMellin_sixth_ne_zero :
    sourceLocalAnnularMellin K P (1 / 6 : ℂ) ≠ 0 := by
  have hz : 0 < (1 / 6 : ℂ).re := by norm_num [Complex.div_re]
  rw [sourceLocalAnnularMellin_eq K P _ hz]
  have hn : ‖(q : ℂ) ^ ((1 / 6 : ℂ) - 1)‖ < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (sourceLocalNorm_pos K P), Complex.sub_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (sourceLocalMellinQ_gt_one K P) (by
      norm_num [Complex.div_re])
  have hd := sourceLocalMellinRatio_norm_lt_one K P (1 / 6 : ℂ) hz
  have hne (a : ℂ) (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
    intro h
    have h' : a = 1 := (sub_eq_zero.mp h).symm
    simp [h'] at ha
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (sourceLocalBall_volume_pos K P 0).ne')
    (Complex.ofReal_ne_zero.mpr (sourceLocalMellinShellMass_pos K P).ne'))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (sourceLocalNorm_pos K P).ne')))) (hne _ hn)) (hne _ hd)

end
end ArtinMatthews.SourcePhysical
