module

public import ArtinMatthews.SpectralJGaussianRadialODE
public import ArtinMatthews.SpectralJGaussianFubini
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-! The radial equation transfers twice to a smooth test supported away from
zero, giving absolute integrability of its actual Bessel transform. -/

namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section

private def radialDensity (f : ℝ → ℂ) (x : ℝ) : ℂ := f x / (x : ℂ)

private def radialFlux (g : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) * deriv g x

/-- The transpose of the radial Bessel operator for integration against (dx). -/
def spectralJRadialAdjoint (f : ℝ → ℂ) : ℝ → ℂ :=
  deriv (radialFlux (radialDensity f))

private theorem radialDensity_tsupport (f : ℝ → ℂ) :
    tsupport (radialDensity f) ⊆ tsupport f := by
  have he : radialDensity f = f * (fun x : ℝ => (x : ℂ)⁻¹) := by
    funext x
    exact div_eq_mul_inv _ _
  rw [he]
  exact tsupport_mul_subset_left

private theorem radialFlux_tsupport (g : ℝ → ℂ) :
    tsupport (radialFlux g) ⊆ tsupport g := by
  exact (tsupport_mul_subset_right (f := fun x : ℝ => (x : ℂ)) (g := deriv g)).trans
    tsupport_deriv_subset

theorem spectralJRadialAdjoint_tsupport_subset (f : ℝ → ℂ) :
    tsupport (spectralJRadialAdjoint f) ⊆ tsupport f :=
  tsupport_deriv_subset.trans ((radialFlux_tsupport _).trans (radialDensity_tsupport f))

private theorem radialDensity_contDiff {f : ℝ → ℂ} {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) : ContDiff ℝ n (radialDensity f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have h0 : (0 : ℝ) ∉ tsupport f := fun h => (lt_irrefl (0 : ℝ)) (mem_Ioi.mp (hpos h))
    have hnear := notMem_tsupport_iff_eventuallyEq.mp h0
    have he : radialDensity f =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [hnear] with x hx
      simp [radialDensity, hx]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hinv : ContDiffAt ℝ n (fun q : ℝ => q⁻¹) x := contDiffAt_id.inv hx
    have hcast : ContDiffAt ℝ n (fun q : ℝ => ((q⁻¹ : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hinv
    have he : radialDensity f = fun q : ℝ => f q * ((q⁻¹ : ℝ) : ℂ) := by
      funext q
      simp [radialDensity, div_eq_mul_inv]
    rw [he]
    exact hf.contDiffAt.mul hcast

private theorem radialFlux_contDiff {g : ℝ → ℂ} {n : ℕ∞ω} (hg : ContDiff ℝ (n + 1) g) :
    ContDiff ℝ n (radialFlux g) := by
  have hderiv := (contDiff_succ_iff_deriv.mp hg).2.2
  exact Complex.ofRealCLM.contDiff.mul hderiv

theorem spectralJRadialAdjoint_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (spectralJRadialAdjoint f) :=
  (contDiff_infty_iff_deriv.mp
    (radialFlux_contDiff (n := ∞) (radialDensity_contDiff hf hpos))).2

private theorem radialDensity_mul_coordinate {f : ℝ → ℂ}
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) (x : ℝ) : radialDensity f x * (x : ℂ) = f x := by
  by_cases hx : x = 0
  · subst x
    have h0 : (0 : ℝ) ∉ tsupport f := fun h => (lt_irrefl (0 : ℝ)) (mem_Ioi.mp (hpos h))
    simp [image_eq_zero_of_notMem_tsupport h0]
  · have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    exact div_mul_cancel₀ _ hx'

private theorem compact_integration_by_parts {u du v dv : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hv : ∀ x, HasDerivAt v (dv x) x)
    (hdu : Continuous du) (hdv : Continuous dv) (huc : HasCompactSupport u) :
    (∫ x, u x * dv x) = -(∫ x, du x * v x) := by
  have hcu : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have hcv : Continuous v := continuous_iff_continuousAt.mpr fun x => (hv x).continuousAt
  have he : du = deriv u := funext fun x => (hu x).deriv.symm
  have hduc : HasCompactSupport du := by rw [he]; exact huc.deriv
  have h₁ : Integrable (u * dv) := (hcu.mul hdv).integrable_of_hasCompactSupport huc.mul_right
  have h₂ : Integrable (du * v) := (hdu.mul hcv).integrable_of_hasCompactSupport hduc.mul_right
  have h₃ : Integrable (u * v) := (hcu.mul hcv).integrable_of_hasCompactSupport huc.mul_right
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hu x) (fun x _ => hv x) h₁ h₂ h₃

private theorem gaussianTransform_eq_integral (f : ℝ → ℂ)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) (w : ℝ) :
    spectralJGaussianTransform f w = ∫ x, f x * spectralJGaussianKernel x w := by
  unfold spectralJGaussianTransform
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hpos h)), zero_mul]

/-- The factor (2/w) follows from the actual frequency (w/2) of the kernel. -/
theorem spectralJGaussianTransform_radial_adjoint (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ))
    (w : ℝ) (hw : 0 < w) :
    spectralJGaussianTransform f w =
      (-(2 : ℂ) / (w : ℂ)) * spectralJGaussianTransform (spectralJRadialAdjoint f) w := by
  let k := fun x : ℝ => spectralJGaussianKernel x w
  let g := radialDensity f
  let c : ℂ := -(w : ℂ) / 2
  have hg : ContDiff ℝ 2 g := radialDensity_contDiff hf hpos
  have hgc : HasCompactSupport g :=
    hfc.of_isClosed_subset (isClosed_tsupport _) (radialDensity_tsupport f)
  have hbg : ContDiff ℝ 1 (radialFlux g) := radialFlux_contDiff (n := 1) hg
  have hbgc : HasCompactSupport (radialFlux g) :=
    hgc.of_isClosed_subset (isClosed_tsupport _) (radialFlux_tsupport g)
  have hck : Continuous k := spectralJGaussianKernel_continuous.curry_left (y := w)
  have hdk : Continuous (deriv k) := spectralJGaussianKernel_deriv_continuous w hw.le
  have hcv : Continuous (fun x : ℝ => c * (x : ℂ)) := continuous_const.mul Complex.continuous_ofReal
  have hcv' : Continuous (fun x : ℝ => c * (x : ℂ) * k x) := hcv.mul hck
  have h₁ : (∫ x, g x * (c * (x : ℂ) * k x)) = -(∫ x, deriv g x * radialFlux k x) :=
    compact_integration_by_parts (u := g) (du := deriv g) (v := radialFlux k)
      (dv := fun x => c * (x : ℂ) * k x)
      (fun x => (hg.differentiable (by simp) x).hasDerivAt)
      (fun x => spectralJGaussianKernel_radial_ode w x hw.le)
      (hg.continuous_deriv (by simp)) hcv' hgc
  have h₂ : (∫ x, radialFlux g x * deriv k x) =
      -(∫ x, spectralJRadialAdjoint f x * k x) :=
    compact_integration_by_parts (u := radialFlux g) (du := deriv (radialFlux g))
      (v := k) (dv := deriv k)
      (fun x => (hbg.differentiable (by simp) x).hasDerivAt)
      (fun x => (spectralJGaussianKernel_differentiable w hw.le x).hasDerivAt)
      (hbg.continuous_deriv (by simp)) hdk hbgc
  have htrans : c * spectralJGaussianTransform f w =
      spectralJGaussianTransform (spectralJRadialAdjoint f) w := by
    rw [gaussianTransform_eq_integral f hpos,
      gaussianTransform_eq_integral _ ((spectralJRadialAdjoint_tsupport_subset f).trans hpos),
      ← integral_const_mul]
    change (∫ x, c * (f x * k x)) = ∫ x, spectralJRadialAdjoint f x * k x
    calc
      _ = ∫ x, g x * (c * (x : ℂ) * k x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← radialDensity_mul_coordinate hpos x]
        change c * (g x * (x : ℂ) * k x) = g x * (c * (x : ℂ) * k x)
        ring
      _ = -(∫ x, deriv g x * radialFlux k x) := h₁
      _ = -(∫ x, radialFlux g x * deriv k x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        unfold radialFlux
        ring
      _ = _ := by rw [h₂, neg_neg]
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hc : (-(2 : ℂ) / (w : ℂ)) * c = 1 := by
    dsimp only [c]
    field_simp <;> ring
  calc
    _ = (-(2 : ℂ) / (w : ℂ)) * (c * spectralJGaussianTransform f w) := by
      rw [← mul_assoc, hc, one_mul]
    _ = _ := by rw [htrans]

theorem spectralJGaussianTransform_linear_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, 0 < w → ‖spectralJGaussianTransform f w‖ ≤ B / w := by
  have hflux : ContDiff ℝ 1 (radialFlux (radialDensity f)) :=
    radialFlux_contDiff (n := 1) (radialDensity_contDiff hf hpos)
  have hcont : Continuous (spectralJRadialAdjoint f) := hflux.continuous_deriv_one
  have hcompact : HasCompactSupport (spectralJRadialAdjoint f) :=
    hfc.of_isClosed_subset (isClosed_tsupport _) (spectralJRadialAdjoint_tsupport_subset f)
  have hi : IntegrableOn (spectralJRadialAdjoint f) (Ioi (0 : ℝ)) :=
    (hcont.integrable_of_hasCompactSupport hcompact).integrableOn
  obtain ⟨B, hB, hb⟩ := spectralJGaussianTransform_bound _ hi
  refine ⟨2 * B, by positivity, ?_⟩
  intro w hw
  rw [spectralJGaussianTransform_radial_adjoint f hf hfc hpos w hw, norm_mul,
    norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo]
  calc
    _ ≤ (2 / w) * B := mul_le_mul_of_nonneg_left (hb w) (by positivity)
    _ = _ := by ring

theorem spectralJGaussianTransform_quadratic_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w → ‖spectralJGaussianTransform f w‖ ≤ C / w ^ 2 := by
  let g := spectralJRadialAdjoint f
  have hgs : ContDiff ℝ ∞ g := spectralJRadialAdjoint_contDiff hf hpos
  have hgc : HasCompactSupport g :=
    hfc.of_isClosed_subset (isClosed_tsupport _) (spectralJRadialAdjoint_tsupport_subset f)
  have hgp : tsupport g ⊆ Ioi (0 : ℝ) := (spectralJRadialAdjoint_tsupport_subset f).trans hpos
  have hg₂s := spectralJRadialAdjoint_contDiff hgs hgp
  have hg₂c : HasCompactSupport (spectralJRadialAdjoint g) :=
    hgc.of_isClosed_subset (isClosed_tsupport _) (spectralJRadialAdjoint_tsupport_subset g)
  have hg₂i : IntegrableOn (spectralJRadialAdjoint g) (Ioi (0 : ℝ)) :=
    (hg₂s.continuous.integrable_of_hasCompactSupport hg₂c).integrableOn
  obtain ⟨B, hB, hbound⟩ := spectralJGaussianTransform_bound _ hg₂i
  refine ⟨4 * B, by positivity, ?_⟩
  intro w hw
  have h₁ := spectralJGaussianTransform_radial_adjoint f (hf.of_le (by simp)) hfc hpos w hw
  have h₂ := spectralJGaussianTransform_radial_adjoint g (hgs.of_le (by simp)) hgc hgp w hw
  change spectralJGaussianTransform f w = (-(2 : ℂ) / (w : ℂ)) *
    spectralJGaussianTransform g w at h₁
  rw [h₁, h₂, ← mul_assoc, ← pow_two, norm_mul]
  have hn : ‖(-(2 : ℂ) / (w : ℂ)) ^ 2‖ = (4 : ℝ) / w ^ 2 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, div_pow]
    norm_num
  rw [hn]
  calc
    _ ≤ (4 / w ^ 2) * B := mul_le_mul_of_nonneg_left (hbound w) (by positivity)
    _ = _ := by ring

theorem spectralJGaussianTransform_integrableOn_tail (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (spectralJGaussianTransform f) (Ioi (2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := spectralJGaussianTransform_quadratic_decay f hf hfc hpos
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.continuous.integrable_of_hasCompactSupport hfc).integrableOn
  have hc := spectralJGaussianTransform_continuous f hf.continuous hfi
  have hmajor := (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2)).const_mul C
  apply hmajor.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hw0 : 0 < w := lt_trans (by norm_num : (0 : ℝ) < 2) hw
  rw [Real.rpow_neg hw0.le, Real.rpow_ofNat, ← div_eq_mul_inv]
  exact hbound w hw0

end
end ArtinMatthews
