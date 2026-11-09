module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGaussianSignal


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier/Mellin identification and the genuine primitive reciprocal
signal criterion. A power improvement at infinity remains an explicit detector
input; all right-line inversion and zero-endpoint hypotheses are proved here. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths OAI.SevenEighths.Continuation
open scoped NumberField nonZeroDivisors Classical Topology FourierTransform
noncomputable section

private theorem primitiveGaussian_line_tendsto_punctured :
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

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveGaussianAmplitude_integrable_reflected :
    Integrable (fun y : ℝ => ψ.primitiveGaussianAmplitude hM hprim ((2 : ℂ)-2*Real.pi*y*I)) := by
  have h := (ψ.primitiveGaussianAmplitude_integrable_line hM hprim hnp 2 le_rfl).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem primitiveGaussianAmplitude_continuous_reflected :
    Continuous (fun y : ℝ => ψ.primitiveGaussianAmplitude hM hprim ((2 : ℂ)-2*Real.pi*y*I)) := by
  have h := (ψ.primitiveGaussianAmplitude_continuous_line hM hprim hnp 2 (by norm_num)).comp
    (show Continuous (fun y : ℝ => -(2*Real.pi)*y) by fun_prop)
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem primitiveGaussianSignal_continuousOn (c : ℝ) :
    ContinuousOn (ψ.primitiveGaussianSignal hM hprim c) (Ioi 0) := by
  let F : ℝ → ℂ := fun y => ψ.primitiveGaussianAmplitude hM hprim (-(((-2 : ℝ) : ℂ)+2*Real.pi*y*I))
  have harg (y : ℝ) : -(((-2 : ℝ) : ℂ)+2*Real.pi*y*I) =
      (2 : ℂ)-2*Real.pi*y*I := by push_cast; ring
  have hF : Integrable F := by
    simpa only [F,harg] using ψ.primitiveGaussianAmplitude_integrable_reflected hM hprim hnp
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
  unfold primitiveGaussianSignal
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul,Complex.ofReal_neg,neg_neg,Complex.ofReal_ofNat,
    F,Pi.mul_apply,Function.comp_apply]

theorem primitiveGaussianSignal_locallyIntegrable (c : ℝ) :
    LocallyIntegrableOn (ψ.primitiveGaussianSignal hM hprim c) (Ioi 0) :=
  (ψ.primitiveGaussianSignal_continuousOn hM hprim hnp c).locallyIntegrableOn measurableSet_Ioi

theorem primitiveGaussianSignal_mellin_eq_amplitude_on_line (c a : ℝ) (ha : a < 2)
    (htop : ψ.primitiveGaussianSignal hM hprim c =O[atTop] (fun x : ℝ => x^(a+c))) (y : ℝ) :
    signalMellin (ψ.primitiveGaussianSignal hM hprim c) c ((2 : ℂ)-2*Real.pi*y*I) =
      ψ.primitiveGaussianAmplitude hM hprim ((2 : ℂ)-2*Real.pi*y*I) := by
  apply signalMellin_eq_on_line _ _ c 2
    (signalMellin_convergent _ a c (ψ.primitiveGaussianSignal_locallyIntegrable hM hprim hnp c)
      htop (ψ.primitiveGaussianSignal_rapidDecayAtZero hM hprim hnp c) (by simpa using ha))
    (ψ.primitiveGaussianAmplitude_integrable_reflected hM hprim hnp)
    (ψ.primitiveGaussianAmplitude_continuous_reflected hM hprim hnp)
  intro x hx
  exact ψ.primitiveGaussianSignal_normalized hM hprim c hx

theorem primitiveGaussianSignal_mellin_eq_amplitude (c a : ℝ) (ha : a < 2)
    (htop : ψ.primitiveGaussianSignal hM hprim c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (ψ.primitiveGaussianSignal hM hprim c) c s =
      ψ.primitiveGaussianAmplitude hM hprim s := by
  have hF := signalMellin_analytic (ψ.primitiveGaussianSignal hM hprim c) a c
    (ψ.primitiveGaussianSignal_locallyIntegrable hM hprim hnp c) htop
    (ψ.primitiveGaussianSignal_rapidDecayAtZero hM hprim hnp c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (ψ.primitiveGaussianSignal hM hprim c) c)
      {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (ψ.primitiveGaussianAmplitude hM hprim)
      {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    exact (ψ.primitiveGaussianAmplitude_differentiableAt hM hprim hnp
      ((le_max_right a 1).trans_lt hz)).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply primitiveGaussian_line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y =>
    ψ.primitiveGaussianSignal_mellin_eq_amplitude_on_line hM hprim hnp c a ha htop y)

theorem primitiveContinued_ne_zero_of_gaussianSignal_power_bound (c a : ℝ) (ha : a < 2)
    (htop : ψ.primitiveGaussianSignal hM hprim c =O[atTop] (fun x : ℝ => x^(a+c)))
    {ρ : ℂ} (hρ : a < ρ.re) : ψ.primitiveContinued hM hprim ρ ≠ 0 := by
  have hL : AnalyticOnNhd ℂ (ψ.primitiveContinued hM hprim) {s : ℂ | a < s.re} :=
    fun s _ => (ψ.primitiveContinued_entire hM hprim).analyticAt s
  have hF := signalMellin_analytic (ψ.primitiveGaussianSignal hM hprim c) a c
    (ψ.primitiveGaussianSignal_locallyIntegrable hM hprim hnp c) htop
    (ψ.primitiveGaussianSignal_rapidDecayAtZero hM hprim hnp c)
  have hW : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp ((s-5/6)^2)) {s : ℂ | a < s.re} := by
    exact ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp
  have heq : ∀ s : ℂ, max a 1 < s.re →
      ψ.primitiveContinued hM hprim s * signalMellin (ψ.primitiveGaussianSignal hM hprim c) c s =
        Complex.exp ((s-5/6)^2) := by
    intro s hs
    rw [ψ.primitiveGaussianSignal_mellin_eq_amplitude hM hprim hnp c a ha htop hs]
    unfold primitiveGaussianAmplitude primitiveReciprocal
    have hn := ψ.primitiveContinued_ne_zero_right hM hprim hnp ((le_max_right a 1).trans_lt hs)
    field_simp
  have hid := product_identity_on_halfPlane a 1 (ψ.primitiveContinued hM hprim)
    (signalMellin (ψ.primitiveGaussianSignal hM hprim c) c) (fun s : ℂ => Complex.exp ((s-5/6)^2))
    hL hF hW heq hρ
  intro hz
  change ψ.primitiveContinued hM hprim ρ * _ = Complex.exp ((ρ-5/6)^2) at hid
  rw [hz,zero_mul] at hid
  exact Complex.exp_ne_zero _ hid.symm

theorem primitiveContinued_ne_zero_of_gaussianProbe_bounds (J : ℝ → ℂ)
    (β ω σ c : ℝ) (hβ : β ≤ 1) (hω : ω < β-7/8) (hσ : 0 < σ)
    (hJ : J =O[atTop] (fun x : ℝ => x^(7/8+c+ω)))
    (herror : (fun x => J x-ψ.primitiveGaussianSignal hM hprim c x) =O[atTop]
      (fun x : ℝ => x^(β+c-σ)))
    {ρ : ℂ} (hρ : β-Supremum.continuationMargin β ω σ < ρ.re) :
    ψ.primitiveContinued hM hprim ρ ≠ 0 := by
  let a := β-Supremum.continuationMargin β ω σ
  have ha : a < 2 := by
    have hp := Supremum.continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have htop : ψ.primitiveGaussianSignal hM hprim c =O[atTop] (fun x : ℝ => x^(a+c)) := by
    have H := common_signal_bound_with_margin J (ψ.primitiveGaussianSignal hM hprim c)
      β ω σ c hJ herror
    convert H using 1
    dsimp [a]
    ring_nf
  exact ψ.primitiveContinued_ne_zero_of_gaussianSignal_power_bound hM hprim hnp c a ha htop hρ

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
