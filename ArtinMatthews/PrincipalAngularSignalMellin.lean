module

public import ArtinMatthews.PrincipalAngularSignalDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin inversion for the literal source signal with its angular correction.
Only the improvement at infinity is an input. Continuity, local integrability,
right-line inversion and rapid decay at zero are derived from the actual Euler
product. Constants and the onset in the infinity estimate may depend on the
field, character and finite set. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology FourierTransform
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

private theorem angularSignal_line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I)
      (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

variable (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
  (S : Finset (ArtinMatthews.ProbePrime K)) (hS : principalAngularCutoff K M ⊆ S)
include hS

theorem principalAngularGaussianAmplitude_integrable_reflected :
    Integrable (fun y : ℝ => principalAngularGaussianAmplitude hζ η S
      ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (principalAngularGaussianAmplitude_integrable_line hζ η S hS 2 le_rfl).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem principalAngularGaussianAmplitude_continuous_reflected :
    Continuous (fun y : ℝ => principalAngularGaussianAmplitude hζ η S
      ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (principalAngularGaussianAmplitude_continuous_line hζ η S hS 2 (by norm_num)).comp
    (show Continuous (fun y : ℝ => -(2 * Real.pi) * y) by fun_prop)
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem principalAngularGaussianSignal_continuousOn :
    ContinuousOn (principalAngularGaussianSignal hζ η S) (Ioi 0) := by
  let F : ℝ → ℂ := fun y => principalAngularGaussianAmplitude hζ η S
    (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I))
  have harg (y : ℝ) : -(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I) =
      (2 : ℂ) - 2 * Real.pi * y * I := by push_cast; ring
  have hF : Integrable F := by
    simpa only [F, harg] using principalAngularGaussianAmplitude_integrable_reflected hζ η S hS
  have hfour : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF
  have hinv : Continuous (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun w : ℝ => 𝓕 F (-w) := funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hfour.comp continuous_neg
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun _ hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log hx.ne').neg.continuousWithinAt
  apply ((hpow (-8 / 15)).mul ((hpow (2 : ℂ)).mul (hinv.comp_continuousOn hlog))).congr
  intro x hx
  unfold principalAngularGaussianSignal
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul, Complex.ofReal_neg, neg_neg, Complex.ofReal_ofNat,
    F, Pi.mul_apply, Function.comp_apply]

theorem principalAngularGaussianSignal_locallyIntegrable :
    LocallyIntegrableOn (principalAngularGaussianSignal hζ η S) (Ioi 0) :=
  (principalAngularGaussianSignal_continuousOn hζ η S hS).locallyIntegrableOn measurableSet_Ioi

theorem principalAngularGaussianSignal_mellin_eq_amplitude_on_line
    (a : ℝ) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ)))) (y : ℝ) :
    signalMellin (principalAngularGaussianSignal hζ η S) (-8 / 15)
      ((2 : ℂ) - 2 * Real.pi * y * I) =
        principalAngularGaussianAmplitude hζ η S ((2 : ℂ) - 2 * Real.pi * y * I) := by
  apply signalMellin_eq_on_line _ _ (-8 / 15) 2
    (signalMellin_convergent _ a (-8 / 15)
      (principalAngularGaussianSignal_locallyIntegrable hζ η S hS) htop
      (principalAngularGaussianSignal_rapidDecayAtZero hζ η S hS) (by simpa using ha))
    (principalAngularGaussianAmplitude_integrable_reflected hζ η S hS)
    (principalAngularGaussianAmplitude_continuous_reflected hζ η S hS)
  intro x hx
  exact principalAngularGaussianSignal_normalized hζ η S hx

theorem principalAngularGaussianSignal_mellin_eq_amplitude
    (a : ℝ) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ))))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (principalAngularGaussianSignal hζ η S) (-8 / 15) s =
      principalAngularGaussianAmplitude hζ η S s := by
  have hF := signalMellin_analytic (principalAngularGaussianSignal hζ η S) a (-8 / 15)
    (principalAngularGaussianSignal_locallyIntegrable hζ η S hS) htop
    (principalAngularGaussianSignal_rapidDecayAtZero hζ η S hS)
  have hFa : AnalyticOnNhd ℂ
      (signalMellin (principalAngularGaussianSignal hζ η S) (-8 / 15))
      {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (principalAngularGaussianAmplitude hζ η S)
      {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    exact (principalAngularGaussianAmplitude_differentiableAt hζ η S hS
      ((le_max_right a 1).trans_lt hz)).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply angularSignal_line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y =>
    principalAngularGaussianSignal_mellin_eq_amplitude_on_line hζ η S hS a ha htop y)

end
end ArtinMatthews.VaryingKummerAnalytic
