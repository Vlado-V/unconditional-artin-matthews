module

public import ArtinMatthews.VaryingKummerAnalyticMixedRadialMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Positive Mellin identity for the actual mixed archimedean Gaussian.
The exp-product substitution is the generic OpenAI RadialIntegrals argument. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
lemma lintegral_exp_product {E : Type*} [MeasureSpace E] [SFinite (volume : Measure E)]
    (f : ℝ × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (Real.exp p.1) * f (Real.exp p.1,p.2)) =
      ∫⁻ t in Ioi 0, ∫⁻ u, f (t,u) := by
  have H := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫⁻ u, f (t,u))
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ] at H
  rw [H, Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro v
  simpa only using lintegral_const_mul' (ENNReal.ofReal (Real.exp v))
    (fun u : E => f (Real.exp v,u)) ENNReal.ofReal_ne_top


variable (K : Type*) [Field K] [NumberField K]

def mixedRealGammaFactor (s : ℝ) : ℝ :=
  ∏ w : InfinitePlace K, (1/2 : ℝ)*Real.pi^(-((InfinitePlace.mult w : ℝ)*s/2))*
    Real.Gamma ((InfinitePlace.mult w : ℝ)*s/2)

theorem mixedRealGammaFactor_ofReal (s : ℝ) :
    (mixedRealGammaFactor K s : ℂ) = mixedGammaFactor K (s : ℂ) := by
  unfold mixedRealGammaFactor mixedGammaFactor
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro w _
  push_cast
  rw [← Complex.Gamma_ofReal, Complex.ofReal_cpow Real.pi_pos.le]
  push_cast
  rfl

theorem mixedRealGammaFactor_pos {s : ℝ} (hs : 0 < s) :
    0 < mixedRealGammaFactor K s := by
  apply Finset.prod_pos
  intro w _
  apply mul_pos
  · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _)
  · apply Real.Gamma_pos_of_pos
    exact div_pos (mul_pos (Nat.cast_pos.mpr InfinitePlace.mult_pos) hs) (by norm_num)

def mixedRealRadialKernel (a : K) (s : ℝ) (t : ℝ) (u : logSpace K) : ℝ :=
  t^((Module.finrank ℚ K : ℝ)*s/2-1) * Real.exp (-Real.pi*t*mixedArchEnergy K a u)

theorem mixedArchEnergy_continuous (a : K) : Continuous (mixedArchEnergy K a) :=
  continuous_finsetSum _ (fun w _ => ((mixedPlaceWeight_continuous K w).mul_const _).pow 2)

theorem mixedRadialKernel_measurable (a : K) (s : ℂ) :
    Measurable (fun p : ℝ × logSpace K => mixedRadialKernel K a s p.1 p.2) := by
  unfold mixedRadialKernel
  have he := mixedArchEnergy_continuous K a
  fun_prop

theorem mixedRadialKernel_product_integrable {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun p : ℝ × logSpace K => mixedRadialKernel K a s p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  refine ⟨(mixedRadialKernel_measurable K a s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [lintegral_prod _ (mixedRadialKernel_measurable K a s).norm.ennreal_ofReal.aemeasurable]
  rw [← lintegral_exp_product _ (mixedRadialKernel_measurable K a s).norm.ennreal_ofReal]
  have he (p : ℝ × logSpace K) :
      ENNReal.ofReal (Real.exp p.1) * ENNReal.ofReal ‖mixedRadialKernel K a s (Real.exp p.1) p.2‖ =
      ENNReal.ofReal ‖mixedLogRadialKernel K a s p‖ := by
    rw [mixedLogRadialKernel_eq_radial, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [he]
  have hi := (mixedLogRadialKernel_integrable K ha hs).hasFiniteIntegral
  rwa [hasFiniteIntegral_iff_norm] at hi

theorem mixedRadialKernel_ofReal (a : K) (s : ℝ) {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    mixedRadialKernel K a (s : ℂ) t u = (mixedRealRadialKernel K a s t u : ℂ) := by
  unfold mixedRadialKernel mixedRealRadialKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_exp]
  push_cast
  congr 2
  all_goals ring

theorem mixedRadialKernel_norm (a : K) (s : ℂ) {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ‖mixedRadialKernel K a s t u‖ = mixedRealRadialKernel K a s.re t u := by
  unfold mixedRadialKernel mixedRealRadialKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.one_re,
    Complex.neg_re, Complex.ofReal_re]
  congr 2
  all_goals ring

theorem mixedRealRadialKernel_integrable {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × logSpace K => mixedRealRadialKernel K a s p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (mixedRadialKernel_product_integrable K ha (s := (s : ℂ)) hs).norm.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)] with p hp
  exact mixedRadialKernel_norm K a (s : ℂ) hp p.2

theorem mixedRealRadialKernel_integral {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi 0, ∫ u, mixedRealRadialKernel K a s t u) =
      mixedRadialJacobian K * mixedRealGammaFactor K s * |(Algebra.norm ℚ a : ℝ)|^(-s) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have he : (∫ t in Ioi 0, ((∫ u, mixedRealRadialKernel K a s t u : ℝ) : ℂ)) =
      ∫ t in Ioi 0, ∫ u, mixedRadialKernel K a (s : ℂ) t u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp_rw [mixedRadialKernel_ofReal K a s ht, integral_complex_ofReal]
  rw [he, mixedRadialKernel_mellin K ha (s := (s : ℂ)) hs]
  push_cast
  rw [mixedRealGammaFactor_ofReal, Complex.ofReal_cpow (abs_nonneg _), Complex.ofReal_neg]

theorem mixedArchGaussian_mellin_lintegral {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s/2-1)) *
      ∫⁻ u, mixedArchGaussian K a t u) =
      ENNReal.ofReal (mixedRadialJacobian K * mixedRealGammaFactor K s *
        |(Algebra.norm ℚ a : ℝ)|^(-s)) := by
  have hi := mixedRealRadialKernel_integrable K ha hs
  have hm : Measurable (fun p : ℝ × logSpace K =>
      mixedRealRadialKernel K a s p.1 p.2) := by
    unfold mixedRealRadialKernel
    have he := mixedArchEnergy_continuous K a
    fun_prop
  have hnn : 0 ≤ᵐ[(volume.restrict (Ioi 0)).prod volume]
      (fun p : ℝ × logSpace K => mixedRealRadialKernel K a s p.1 p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    exact mul_nonneg (Real.rpow_nonneg hp.le _) (Real.exp_pos _).le
  rw [← mixedRealRadialKernel_integral K ha hs, ← integral_prod _ hi,
    ofReal_integral_eq_lintegral_ofReal hi hnn,
    lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [mixedRealRadialKernel, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rfl

end
end ArtinMatthews.VaryingKummerAnalytic
