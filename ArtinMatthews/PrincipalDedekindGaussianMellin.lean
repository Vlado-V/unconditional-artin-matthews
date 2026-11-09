module

public import ArtinMatthews.PrincipalDedekindGaussianSignal


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier/Mellin identification for the pole-removed Dedekind reciprocal.
A power bound at infinity remains an explicit detector input; all inversion,
zero-endpoint, and regularized analytic hypotheses are derived. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths OAI.SevenEighths.Continuation
open scoped NumberField nonZeroDivisors Classical Topology FourierTransform
noncomputable section

private theorem principalGaussian_line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ)-2*Real.pi*y*I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ)-2*Real.pi*y*I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

variable (K : Type*) [Field K] [NumberField K]

theorem principalGaussianAmplitude_integrable_reflected :
    Integrable (fun y : ℝ => principalGaussianAmplitude K ((2 : ℂ)-2*Real.pi*y*I)) := by
  have h := (principalGaussianAmplitude_integrable_line K 2 le_rfl).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem principalGaussianAmplitude_continuous_reflected :
    Continuous (fun y : ℝ => principalGaussianAmplitude K ((2 : ℂ)-2*Real.pi*y*I)) := by
  have h := (principalGaussianAmplitude_continuous_line K 2 (by norm_num)).comp
    (show Continuous (fun y : ℝ => -(2*Real.pi)*y) by fun_prop)
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem principalGaussianSignal_continuousOn (c : ℝ) :
    ContinuousOn (principalGaussianSignal K c) (Ioi 0) := by
  let F : ℝ → ℂ := fun y => principalGaussianAmplitude K (-(((-2 : ℝ) : ℂ)+2*Real.pi*y*I))
  have harg (y : ℝ) : -(((-2 : ℝ) : ℂ)+2*Real.pi*y*I) =
      (2 : ℂ)-2*Real.pi*y*I := by push_cast; ring
  have hF : Integrable F := by
    simpa only [F,harg] using principalGaussianAmplitude_integrable_reflected K
  have hfour : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF
  have hinv : Continuous (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun w : ℝ => 𝓕 F (-w) := funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hfour.comp continuous_neg
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ)^z) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (fun _ hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log hx.ne').neg.continuousWithinAt
  apply ((hpow (c : ℂ)).mul ((hpow (2 : ℂ)).mul (hinv.comp_continuousOn hlog))).congr
  intro x hx
  unfold principalGaussianSignal
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul,Complex.ofReal_neg,neg_neg,Complex.ofReal_ofNat,
    F,Pi.mul_apply,Function.comp_apply]

theorem principalGaussianSignal_locallyIntegrable (c : ℝ) :
    LocallyIntegrableOn (principalGaussianSignal K c) (Ioi 0) :=
  (principalGaussianSignal_continuousOn K c).locallyIntegrableOn measurableSet_Ioi

theorem principalGaussianSignal_mellin_eq_amplitude_on_line (c a : ℝ) (ha : a < 2)
    (htop : principalGaussianSignal K c =O[atTop] (fun x : ℝ => x^(a+c))) (y : ℝ) :
    signalMellin (principalGaussianSignal K c) c ((2 : ℂ)-2*Real.pi*y*I) =
      principalGaussianAmplitude K ((2 : ℂ)-2*Real.pi*y*I) := by
  apply signalMellin_eq_on_line _ _ c 2
    (signalMellin_convergent _ a c (principalGaussianSignal_locallyIntegrable K c)
      htop (principalGaussianSignal_rapidDecayAtZero K c) (by simpa using ha))
    (principalGaussianAmplitude_integrable_reflected K)
    (principalGaussianAmplitude_continuous_reflected K)
  intro x hx
  exact principalGaussianSignal_normalized K c hx

theorem principalGaussianSignal_mellin_eq_amplitude (c a : ℝ) (ha : a < 2)
    (htop : principalGaussianSignal K c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (principalGaussianSignal K c) c s =
      principalGaussianAmplitude K s := by
  have hF := signalMellin_analytic (principalGaussianSignal K c) a c
    (principalGaussianSignal_locallyIntegrable K c) htop
    (principalGaussianSignal_rapidDecayAtZero K c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (principalGaussianSignal K c) c)
      {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (principalGaussianAmplitude K)
      {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    exact (principalGaussianAmplitude_differentiableAt K
      ((le_max_right a 1).trans_lt hz)).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply principalGaussian_line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y =>
    principalGaussianSignal_mellin_eq_amplitude_on_line K c a ha htop y)

theorem principalDedekindRegularized_ne_zero_of_gaussianSignal_power_bound (c a : ℝ) (ha : a < 2)
    (htop : principalGaussianSignal K c =O[atTop] (fun x : ℝ => x^(a+c)))
    {ρ : ℂ} (hρ : a < ρ.re) : principalDedekindRegularized K ρ ≠ 0 := by
  have hL : AnalyticOnNhd ℂ (principalDedekindRegularized K) {s : ℂ | a < s.re} :=
    fun s _ => (principalDedekindRegularized_entire K).analyticAt s
  have hF := signalMellin_analytic (principalGaussianSignal K c) a c
    (principalGaussianSignal_locallyIntegrable K c) htop
    (principalGaussianSignal_rapidDecayAtZero K c)
  have hW : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp ((s-5/6)^2)) {s : ℂ | a < s.re} := by
    exact ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp
  have heq : ∀ s : ℂ, max a 1 < s.re →
      principalDedekindRegularized K s * signalMellin (principalGaussianSignal K c) c s =
        Complex.exp ((s-5/6)^2) := by
    intro s hs
    rw [principalGaussianSignal_mellin_eq_amplitude K c a ha htop hs]
    unfold principalGaussianAmplitude principalDedekindReciprocal
    have hn := principalDedekindRegularized_ne_zero_right K ((le_max_right a 1).trans_lt hs)
    field_simp
  have hid := product_identity_on_halfPlane a 1 (principalDedekindRegularized K)
    (signalMellin (principalGaussianSignal K c) c) (fun s : ℂ => Complex.exp ((s-5/6)^2))
    hL hF hW heq hρ
  intro hz
  change principalDedekindRegularized K ρ * _ = Complex.exp ((ρ-5/6)^2) at hid
  rw [hz,zero_mul] at hid
  exact Complex.exp_ne_zero _ hid.symm

theorem principalDedekindRegularized_ne_zero_of_gaussianProbe_bounds (J : ℝ → ℂ)
    (β ω σ c : ℝ) (hβ : β ≤ 1) (hω : ω < β-7/8) (hσ : 0 < σ)
    (hJ : J =O[atTop] (fun x : ℝ => x^(7/8+c+ω)))
    (herror : (fun x => J x-principalGaussianSignal K c x) =O[atTop]
      (fun x : ℝ => x^(β+c-σ)))
    {ρ : ℂ} (hρ : β-Supremum.continuationMargin β ω σ < ρ.re) :
    principalDedekindRegularized K ρ ≠ 0 := by
  let a := β-Supremum.continuationMargin β ω σ
  have ha : a < 2 := by
    have hp := Supremum.continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have htop : principalGaussianSignal K c =O[atTop] (fun x : ℝ => x^(a+c)) := by
    have H := common_signal_bound_with_margin J (principalGaussianSignal K c)
      β ω σ c hJ herror
    convert H using 1
    dsimp [a]
    ring_nf
  exact principalDedekindRegularized_ne_zero_of_gaussianSignal_power_bound K c a ha htop hρ

theorem mixedDedekindZeta_ne_zero_of_principalGaussianSignal_power_bound
    (c a : ℝ) (ha : a < 2)
    (htop : principalGaussianSignal K c =O[atTop] (fun x : ℝ => x^(a+c)))
    {ρ : ℂ} (hρ : a < ρ.re) (hρ1 : ρ ≠ 1) : mixedDedekindZeta K ρ ≠ 0 := by
  unfold mixedDedekindZeta
  exact div_ne_zero
    (principalDedekindRegularized_ne_zero_of_gaussianSignal_power_bound K c a ha htop hρ)
    (sub_ne_zero.mpr hρ1)

theorem mixedDedekindZeta_ne_zero_of_principalGaussianProbe_bounds
    (J : ℝ → ℂ) (β ω σ c : ℝ) (hβ : β ≤ 1) (hω : ω < β-7/8) (hσ : 0 < σ)
    (hJ : J =O[atTop] (fun x : ℝ => x^(7/8+c+ω)))
    (herror : (fun x => J x-principalGaussianSignal K c x) =O[atTop]
      (fun x : ℝ => x^(β+c-σ)))
    {ρ : ℂ} (hρ : β-Supremum.continuationMargin β ω σ < ρ.re) (hρ1 : ρ ≠ 1) :
    mixedDedekindZeta K ρ ≠ 0 := by
  unfold mixedDedekindZeta
  exact div_ne_zero
    (principalDedekindRegularized_ne_zero_of_gaussianProbe_bounds K J β ω σ c
      hβ hω hσ hJ herror hρ) (sub_ne_zero.mpr hρ1)

end
end ArtinMatthews.VaryingKummerAnalytic
