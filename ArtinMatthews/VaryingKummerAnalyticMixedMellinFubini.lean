module

public import ArtinMatthews.VaryingKummerAnalyticMixedXiMellin
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartial


set_option backward.privateInPublic true
@[expose] public section

/-! Actual absolute convergence and Fubini for the mixed ideal theta Mellin
integral, using the genuine convergent Dedekind ideal series. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedThetaMellinKernel_integrable {s : ℂ} (hs : 1 < s.re) :
    Integrable (mixedThetaMellinKernel K I s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) := by
  refine ⟨(mixedThetaMellinKernel_measurable K I s).aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖mixedThetaMellinKernel K I s p‖ₑ
    ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) < ⊤
  rw [mixedThetaMellinKernel_enorm_integral K I s (lt_trans zero_lt_one hs)]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
    ENNReal.ofReal_lt_top) (mixedPartialDedekindPositive_lt_top K I hs)

theorem mixedUnitThetaMellin_eq_integral {s : ℂ} (hs : 1 < s.re) :
    mixedUnitThetaMellin K I s =
      ∫ p, mixedThetaMellinKernel K I s p
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K)) :=
  (integral_prod_symm _ (mixedThetaMellinKernel_integrable K I hs)).symm

theorem mixedThetaMellinKernel_real_eq_norm (s : ℝ) {t : ℝ} (ht : 0 < t)
    (u : logSpace K) :
    mixedThetaMellinKernel K I (s : ℂ) (t,u) =
      ((‖mixedThetaMellinKernel K I (s : ℂ) (t,u)‖ : ℝ) : ℂ) := by
  rw [mixedThetaMellinKernel_norm K I (s : ℂ) ht u]
  unfold mixedThetaMellinKernel
  rw [mixedIdealFlowTheta_sub_one_real K I u ht,
    Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
  push_cast
  rfl

theorem mixedUnitThetaMellin_real (s : ℝ) (hs : 1 < s) :
    mixedUnitThetaMellin K I (s : ℂ) =
      (((torsionOrder K : ℝ) *
        (mixedRealHeckeFactor K s * (FractionalIdeal.absNorm I.1 : ℝ)^(-s)) *
          (mixedPartialDedekindPositive K I s).toReal : ℝ) : ℂ) := by
  let μ := (volume.restrict (Ioi (0 : ℝ))).prod
    (volume.restrict (mixedUnitLogDomain K))
  have hi := mixedThetaMellinKernel_integrable K I (s := (s : ℂ)) hs
  rw [mixedUnitThetaMellin_eq_integral K I (s := (s : ℂ)) hs]
  calc
    _ = ∫ p, ((‖mixedThetaMellinKernel K I (s : ℂ) p‖ : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)] with p hp
      exact mixedThetaMellinKernel_real_eq_norm K I s hp p.2
    _ = ((∫ p, ‖mixedThetaMellinKernel K I (s : ℂ) p‖ ∂μ : ℝ) : ℂ) := integral_complex_ofReal
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        hi.norm.aestronglyMeasurable]
      simp_rw [ofReal_norm]
      rw [mixedThetaMellinKernel_enorm_integral K I (s : ℂ) (lt_trans zero_lt_one hs)]
      simp only [Complex.ofReal_re, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (mul_nonneg (mixedRealHeckeFactor_pos K (lt_trans zero_lt_one hs)).le
          (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _))]

theorem mixedIdealUnitXi_real_eq_partial (s : ℝ) (hs : 1 < s) :
    mixedIdealUnitXi K I (s : ℂ) =
      ((Module.finrank ℚ K : ℂ)*(s : ℂ)/2) *
        ((Module.finrank ℚ K : ℂ)*(s : ℂ)/2 - (Module.finrank ℚ K : ℂ)/2) *
      (((torsionOrder K : ℝ) *
        (mixedRealHeckeFactor K s * (FractionalIdeal.absNorm I.1 : ℝ)^(-s)) *
          (mixedPartialDedekindPositive K I s).toReal : ℝ) : ℂ) := by
  rw [mixedIdealUnitXi_eq_unitMellin K I hs, mixedUnitThetaMellin_real K I s hs]

end
end ArtinMatthews.VaryingKummerAnalytic
