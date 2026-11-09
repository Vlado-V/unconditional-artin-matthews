module

public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinResidues


set_option backward.privateInPublic true
@[expose] public section

/-! The proved prime-power Mellin identity uses the same literal canonical
integrand as the meromorphic contour argument on its initial right line. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

variable (K : Type*) [Field K] [NumberField K]

theorem mixedDedekindZeta_logDeriv_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv (mixedDedekindZeta K) s = logDeriv (NumberField.dedekindZeta K) s := by
  have he : mixedDedekindZeta K =ᶠ[𝓝 s] NumberField.dedekindZeta K := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact mixedDedekindZeta_eq K hz
  exact (logDeriv_congr_nhds he).eq_of_nhds

theorem mixedExplicitFormulaIntegrand_eq_primePower_mellin (f : ℝ → ℂ) (x : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    mixedExplicitFormulaIntegrand K f x s =
      (x : ℂ)^s*(-logDeriv (NumberField.dedekindZeta K) s)*mellin f s := by
  rw [mixedExplicitFormulaIntegrand, mixedDedekindZeta_logDeriv_eq_of_one_lt_re K hs]
  ring

theorem dedekindPrimePower_canonical_mellin_integrable
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => mixedExplicitFormulaIntegrand K f x ((σ : ℂ)+t*Complex.I)) := by
  exact (dedekindPrimePower_mellin_integrable K f hcompact hpositive hsmooth hx hσ).congr
    (Eventually.of_forall fun t =>
      (mixedExplicitFormulaIntegrand_eq_primePower_mellin K f x (s := (σ : ℂ)+t*Complex.I)
        (by simpa using hσ)).symm)

theorem dedekindPrimePower_smoothed_canonical_mellin
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∑' i : DedekindPrimePowerIndex K,
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)) =
      ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
        mixedExplicitFormulaIntegrand K f x ((σ : ℂ)+t*Complex.I)) := by
  rw [dedekindPrimePower_smoothed_mellin K f hcompact hpositive hsmooth hx hσ]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t =>
    (mixedExplicitFormulaIntegrand_eq_primePower_mellin K f x (s := (σ : ℂ)+t*Complex.I)
      (by simpa using hσ)).symm

end
end ArtinMatthews.VaryingKummerAnalytic
