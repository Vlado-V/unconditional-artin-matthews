module

public import ArtinMatthews.SpectralBesselI


set_option backward.privateInPublic true
@[expose] public section

/-! The actual beta integral on the open unit interval, with absolute
convergence.  Endpoints are discarded only using their zero Lebesgue measure. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralUnitBetaProfile (a b : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)^(a-1)*(1-(t : ℂ))^(b-1)

theorem spectralUnitBetaProfile_integrable (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (spectralUnitBetaProfile a b) (Ioo (0 : ℝ) 1) := by
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
    (Complex.betaIntegral_convergent ha hb)

theorem spectralUnitBetaProfile_integral (a b : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, spectralUnitBetaProfile a b t) = Complex.betaIntegral a b := by
  rw [Complex.betaIntegral,intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  rfl

theorem spectralUnitBetaProfile_norm (a b : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖spectralUnitBetaProfile a b t‖ = t^(a.re-1)*(1-t)^(b.re-1) := by
  unfold spectralUnitBetaProfile
  rw [norm_mul]
  have he : 1-(t : ℂ) = ((1-t : ℝ) : ℂ) := by push_cast; rfl
  rw [he,Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
    Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht.2)]
  simp only [Complex.sub_re,Complex.one_re]

end ArtinMatthews
