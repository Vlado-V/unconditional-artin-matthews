module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun


set_option backward.privateInPublic true
@[expose] public section

/-! Generic one-dimensional weak-derivative primitives extracted with their
proof bodies unchanged from OAI.Analysis.LiebThirring.SobolevProjection,
first three lemmas, plus CutoffEnergy's local-L1 interval helper.
Only Mathlib is imported; no Lieb--Thirring operator/model is introduced. -/
namespace ArtinMatthews.SpectralCuspWeakRegularity
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff

lemma locallyIntegrable_intervalIntegrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff').mpr (hf.integrableOn_isCompact isCompact_uIcc)

/-- A locally integrable function whose distributional derivative vanishes is constant.
This uses only smooth compact tests, hence applies to the H¹ definition. -/
lemma ae_const_of_weak_derivative_zero {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = 0) : ∃ c : ℝ, f =ᵐ[volume] fun _ ↦ c := by
  have hc (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
      ∀ x y : ℝ, (ρ ⋆[lsmul ℝ ℝ, volume] f) x = (ρ ⋆[lsmul ℝ ℝ, volume] f) y := by
    have hder (x : ℝ) : HasDerivAt (ρ ⋆[lsmul ℝ ℝ, volume] f) 0 x := by
      have hd := hρc.hasDerivAt_convolution_left (lsmul ℝ ℝ) (hρ.of_le (by simp)) hf x
      have ht := hw (fun y ↦ ρ (x-y)) (hρ.comp (contDiff_const.sub contDiff_id))
        (hρc.comp_homeomorph (Homeomorph.subLeft x))
      have hdφ (y : ℝ) : deriv (fun y ↦ ρ (x-y)) y = -deriv ρ (x-y) := by
        simpa only [Function.comp_def, zero_sub, mul_neg, mul_one] using
          ((hρ.differentiable (by simp) (x-y)).hasDerivAt.comp y
            ((hasDerivAt_const y x).sub (hasDerivAt_id y))).deriv
      simp_rw [hdφ,mul_neg,integral_neg] at ht
      have hz : ((deriv ρ ⋆[lsmul ℝ ℝ, volume] f) x) = 0 := by
        rw [convolution_eq_swap]
        simpa only [lsmul_apply,smul_eq_mul,mul_comm,neg_eq_zero] using ht
      rwa [hz] at hd
    exact is_const_of_deriv_eq_zero (fun x ↦ (hder x).differentiableAt)
      (fun x ↦ (hder x).deriv)
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n ↦
    ⟨(n+1 : ℝ)⁻¹,2*(n+1 : ℝ)⁻¹,by positivity,by nlinarith [inv_pos.mpr (show (0 : ℝ)<n+1 by positivity)]⟩
  have hb : Tendsto (fun n ↦ (b n).rOut) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ ↦ (n+1 : ℝ)⁻¹) atTop (𝓝 0) :=
      by simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero] using ht.const_mul 2
  have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := b) hb (K := 2) (Eventually.of_forall (fun _ ↦ le_refl _)) hf
  obtain ⟨x₀,hx₀⟩ := ha.exists
  refine ⟨f x₀,?_⟩
  filter_upwards [ha] with x hx
  apply tendsto_nhds_unique hx
  convert hx₀ using 1
  funext n
  exact hc ((b n).normed volume) (b n).contDiff_normed (b n).hasCompactSupport_normed x x₀


lemma primitive_weak_derivative {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, (∫ t in (0 : ℝ)..x, g t) * deriv φ x) = -(∫ x, g x * φ x) := by
  obtain ⟨R,hR,hRs⟩ := hφc.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hs : tsupport φ ⊆ Ioo (-R) R := by
    intro x hx
    have hh := hRs hx
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt,mem_Ioo] using hh
  have hzero : φ (-R) = 0 ∧ φ R = 0 := by
    constructor <;> apply image_eq_zero_of_notMem_tsupport <;>
      intro h <;> have := hs h <;> simp_all
  let F := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hgi := locallyIntegrable_intervalIntegrable hg (-R) R
  have h0 : (0 : ℝ) ∈ uIcc (-R) R := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have hF : AbsolutelyContinuousOnInterval F (-R) R :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral h0
  have hφa : AbsolutelyContinuousOnInterval φ (-R) R :=
    (hφ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hfd : ∀ᵐ x, x ∈ uIcc (-R) R → deriv F x = g x := by
    filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hmem
    exact (hx hmem 0 h0).deriv
  have he := hF.integral_mul_deriv_eq_deriv_mul hφa
  rw [hzero.1,hzero.2,mul_zero,mul_zero,sub_self,zero_sub] at he
  have hi : (∫ x in (-R)..R, deriv F x * φ x) = ∫ x in (-R)..R, g x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfd] with x hx hmem
    rw [hx (uIoc_subset_uIcc hmem)]
  rw [hi] at he
  have hleft : Function.support (fun x ↦ F x * deriv φ x) ⊆ Ioc (-R) R := by
    intro x hx
    have hd : x ∈ tsupport (deriv φ) :=
      subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)
    exact Ioo_subset_Ioc_self (hs (tsupport_deriv_subset hd))
  have hright : Function.support (fun x ↦ g x * φ x) ⊆ Ioc (-R) R := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs (subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)))
  rwa [intervalIntegral.integral_eq_integral_of_support_subset hleft,
    intervalIntegral.integral_eq_integral_of_support_subset hright] at he

/-- The precise one-dimensional Sobolev representative, obtained from the weak derivative
without assuming any pointwise regularity or adding a representative to the domain. -/
lemma weak_derivative_representation {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = -(∫ x, g x * φ x)) :
    ∃ c : ℝ, f =ᵐ[volume] fun x ↦ c + ∫ t in (0 : ℝ)..x, g t := by
  let F := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hFc : Continuous F := intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable hg) 0
  obtain ⟨c,hc⟩ := ae_const_of_weak_derivative_zero (hf.sub hFc.locallyIntegrable) (fun φ hφ hφc ↦ by
    have hi₁ : Integrable (fun x ↦ f x * deriv φ x) volume :=
      hf.integrable_smul_right_of_hasCompactSupport (hφ.continuous_deriv (by simp)) hφc.deriv
    have hi₂ : Integrable (fun x ↦ F x * deriv φ x) volume :=
      hFc.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hφc.deriv
    simp only [Pi.sub_apply,sub_mul,integral_sub hi₁ hi₂,hw φ hφ hφc]
    change -(∫ x, g x * φ x) - (∫ x, (∫ t in (0 : ℝ)..x, g t) * deriv φ x) = 0
    rw [primitive_weak_derivative hg φ hφ hφc,sub_self])
  refine ⟨c,?_⟩
  filter_upwards [hc] with x hx
  exact sub_eq_iff_eq_add.mp hx


end
end ArtinMatthews.SpectralCuspWeakRegularity
