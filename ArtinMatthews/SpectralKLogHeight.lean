module

public import ArtinMatthews.SpectralFiniteFourierFrame


set_option backward.privateInPublic true
@[expose] public section

/-! Exact logarithmic height transport for the actual real K kernel.
The finite interval substitution uses the genuine Jacobian dx/x. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews

theorem spectral_scaledExp_Ioc_image {k : ℝ} (hk : 0 < k) (a b : ℝ) :
    (fun u : ℝ => k*Real.exp u) '' Ioc a b = Ioc (k*Real.exp a) (k*Real.exp b) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hu.1) hk,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hk.le⟩
  · intro hx
    have hx0 : 0 < x := (mul_pos hk (Real.exp_pos _)).trans hx.1
    let u := Real.log (x/k)
    have he : k*Real.exp u = x := by
      rw [show Real.exp u = x/k from Real.exp_log (div_pos hx0 hk)]
      exact mul_div_cancel₀ x hk.ne'
    refine ⟨u,⟨?_,?_⟩,he⟩
    · apply Real.exp_lt_exp.mp
      apply (mul_lt_mul_iff_of_pos_left hk).mp
      rw [he]
      exact hx.1
    · apply Real.exp_le_exp.mp
      apply (mul_le_mul_iff_of_pos_left hk).mp
      rw [he]
      exact hx.2

theorem spectral_scaledExp_Ioc_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) {k : ℝ} (hk : 0 < k) (a b : ℝ) :
    (∫ u in Ioc a b, F (k*Real.exp u)) =
      ∫ x in Ioc (k*Real.exp a) (k*Real.exp b), x⁻¹ • F x := by
  have hderiv (u : ℝ) :
      HasDerivAt (fun v : ℝ => k*Real.exp v) (k*Real.exp u) u :=
    (Real.hasDerivAt_exp u).const_mul k
  have hmono : StrictMono (fun v : ℝ => k*Real.exp v) :=
    fun _ _ h => mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr h) hk
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioc a b) measurableSet_Ioc
    (fun u _ => (hderiv u).hasDerivWithinAt) hmono.injective.injOn (fun x => x⁻¹ • F x)
  rw [spectral_scaledExp_Ioc_image hk a b] at h
  refine (setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)).trans h.symm
  have hp : 0 < k*Real.exp u := mul_pos hk (Real.exp_pos _)
  simp only [abs_of_pos hp,smul_smul,mul_inv_cancel₀ hp.ne',one_smul]

theorem spectral_scaledExp_Ioc_nonneg_moment_bound (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hI : IntegrableOn F (Ioi (0 : ℝ))) {k : ℝ} (hk : 0 < k) (a b : ℝ) :
    (∫ u in Ioc a b, F (k*Real.exp u)) ≤
      (k*Real.exp a)⁻¹*(∫ x in Ioi (0 : ℝ), F x) := by
  let A := k*Real.exp a
  let B := k*Real.exp b
  have hA : 0 < A := mul_pos hk (Real.exp_pos _)
  have hS : Ioc A B ⊆ Ioi (0 : ℝ) :=
    Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hA.le)
  have hI₁ := hI.mono_set hS
  have hInv : ContinuousOn (fun x : ℝ => x⁻¹) (Icc A B) :=
    continuousOn_id.inv₀ (fun x hx => (hA.trans_le hx.1).ne')
  have hI₂ : IntegrableOn (fun x : ℝ => x⁻¹*F x) (Ioc A B) :=
    hI₁.continuousOn_mul_of_subset hInv isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  rw [spectral_scaledExp_Ioc_integral F hk a b]
  change (∫ x in Ioc A B, x⁻¹*F x) ≤ A⁻¹*(∫ x in Ioi (0 : ℝ), F x)
  calc
    _ ≤ ∫ x in Ioc A B, A⁻¹*F x :=
      setIntegral_mono_on hI₂ (hI₁.const_mul _) measurableSet_Ioc
        (fun x hx => mul_le_mul_of_nonneg_right
          (by simpa only [one_div] using one_div_le_one_div_of_le hA hx.1.le) (hF x))
    _ = A⁻¹*(∫ x in Ioc A B, F x) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hI (Filter.Eventually.of_forall hF)
        (Filter.Eventually.of_forall (fun _ hx => hS hx))) (inv_nonneg.mpr hA.le)

theorem spectralKLRealKernel_deriv_continuousOn (t : ℝ) :
    ContinuousOn (deriv (spectralKLRealKernel t)) (Ioi (0 : ℝ)) := by
  let ν := (t : ℂ)*Complex.I
  have h : ContinuousOn (fun x => deriv (OAI.CubicEisenstein.schlafliBesselK ν) x) (Ioi (0 : ℝ)) := by
    intro x hx
    exact (schlafliBesselK_deriv_hasDerivAt ν x hx).continuousAt.continuousWithinAt
  have hre := Complex.continuous_re.comp_continuousOn h
  exact hre.congr (fun x hx => (spectralKLRealKernel_hasDerivAt_re t hx).deriv)

def spectralRealKLogKernel (k t u : ℝ) : ℝ := spectralKLRealKernel t (k*Real.exp u)

theorem spectralRealKLogKernel_hasDerivAt {k : ℝ} (hk : 0 < k) (t u : ℝ) :
    HasDerivAt (spectralRealKLogKernel k t) ((k*Real.exp u)*deriv (spectralKLRealKernel t) (k*Real.exp u)) u := by
  have hx : 0 < k*Real.exp u := mul_pos hk (Real.exp_pos _)
  have hK := spectralKLRealKernel_hasDerivAt_re t hx
  have h := hK.comp u ((Real.hasDerivAt_exp u).const_mul k)
  convert h using 1
  · rfl
  · rw [hK.deriv,mul_comm]

theorem spectralRealKLogKernel_contDiff_one {k : ℝ} (hk : 0 < k) (t : ℝ) :
    ContDiff ℝ 1 (spectralRealKLogKernel k t) := by
  have hc : Continuous (fun u : ℝ => k*Real.exp u) := continuous_const.mul Real.continuous_exp
  have hd : Continuous (fun u : ℝ => deriv (spectralKLRealKernel t) (k*Real.exp u)) := by
    apply continuousOn_univ.mp
    exact (spectralKLRealKernel_deriv_continuousOn t).comp hc.continuousOn
      (fun u _ => mul_pos hk (Real.exp_pos u))
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun u => (spectralRealKLogKernel_hasDerivAt hk t u).differentiableAt,?_⟩
  have he : deriv (spectralRealKLogKernel k t) = fun u => (k*Real.exp u)*deriv (spectralKLRealKernel t) (k*Real.exp u) :=
    funext (fun u => (spectralRealKLogKernel_hasDerivAt hk t u).deriv)
  rw [he]
  exact hc.mul hd

end ArtinMatthews
