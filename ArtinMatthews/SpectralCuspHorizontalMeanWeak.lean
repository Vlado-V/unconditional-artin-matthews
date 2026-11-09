module

public import ArtinMatthews.SpectralCuspProjectedTail
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact-test differentiation of the literal normalized horizontal
mean. Smooth vertical-slice integration by parts and actual product
integrability justify the Fubini interchange. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A compact vertical test and a bounded horizontal cell give genuine
product integrability even when the smooth plane function is not compact. -/
theorem cuspHorizontal_test_product_integrable {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (w : ℝ) :
    Integrable (fun p : ℝ × ℝ => ρ p.2 • F p)
      ((volume.restrict (Ioc (0 : ℝ) w)).prod volume) := by
  let H : ℝ × ℝ → ℂ := fun p => ρ p.2 • F p
  have hH : Continuous H := (hρ.comp continuous_snd).smul hF
  have hi : IntegrableOn H ((Ioc (0 : ℝ) w) ×ˢ tsupport ρ) :=
    (hH.locallyIntegrable.integrableOn_isCompact (isCompact_Icc.prod hρc)).mono_set
      (prod_mono Ioc_subset_Icc_self Subset.rfl)
  change Integrable H ((volume.prod volume).restrict ((Ioc (0 : ℝ) w) ×ˢ tsupport ρ)) at hi
  rw [← Measure.prod_restrict] at hi
  have hir : IntegrableOn H ((univ : Set ℝ) ×ˢ tsupport ρ)
      ((volume.restrict (Ioc (0 : ℝ) w)).prod volume) := by
    change Integrable H (((volume.restrict (Ioc (0 : ℝ) w)).prod volume).restrict
      ((univ : Set ℝ) ×ˢ tsupport ρ))
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hi
  apply (integrableOn_iff_integrable_of_support_subset (s := (univ : Set ℝ) ×ˢ tsupport ρ) ?_).mp hir
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  apply subset_tsupport
  contrapose! hp
  simp only [Function.mem_support, not_not] at hp ⊢
  simp [H, hp]

/-- Exact Fubini transport through the normalized mean. -/
theorem cuspHorizontalMean_test_integral {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (w : ℝ) :
    (∫ y, ρ y • cuspHorizontalMean w F y) =
      (w : ℂ)⁻¹ * ∫ x in Ioc (0 : ℝ) w, ∫ y, ρ y • F (x, y) := by
  have he (y : ℝ) : ρ y • cuspHorizontalMean w F y =
      (w : ℂ)⁻¹ * ∫ x in Ioc (0 : ℝ) w, ρ y • F (x, y) := by
    rw [integral_smul]
    simp only [cuspHorizontalMean, Complex.real_smul]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  exact (integral_integral_swap (cuspHorizontal_test_product_integrable hF hρ hρc w)).symm

/-- Both test pairings with the actual mean are absolutely integrable. -/
theorem cuspHorizontalMean_test_integrable {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (w : ℝ) :
    Integrable (fun y => ρ y • cuspHorizontalMean w F y) volume :=
  (cuspHorizontalMean_continuous hF w).locallyIntegrable
    |>.integrable_smul_left_of_hasCompactSupport hρ hρc

/-- A genuine compact-test integration by parts for one smooth vertical
slice, with its actual physical vertical derivative. -/
theorem cuspPlaneSlice_weak_verticalDerivative {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (x : ℝ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    (∫ y, deriv ρ y • F (x, y)) =
      -(∫ y, ρ y • fderiv ℝ F (x, y) (0, 1)) := by
  have hfc : Continuous (fun y : ℝ => F (x, y)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hdc : Continuous (fun y : ℝ => fderiv ℝ F (x, y) (0, 1)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_apply
      continuous_const
  have hfd (y : ℝ) : HasDerivAt (fun t : ℝ => F (x, t))
      (fderiv ℝ F (x, y) (0, 1)) y := by
    simpa only [Function.comp_def] using
      ((hF.differentiable (by simp) (x, y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  have hi : Integrable (fun y => ρ y • fderiv ℝ F (x, y) (0, 1)) volume :=
    hdc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
  have hi' : Integrable (fun y => deriv ρ y • F (x, y)) volume :=
    hfc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    (hρ.continuous_deriv (by simp)) hρc.deriv
  have hi0 : Integrable (fun y => ρ y • F (x, y)) volume :=
    hfc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
  have H := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (fun y _ => (hρ.differentiable (by simp) y).hasDerivAt)
    (fun y _ => hfd y) hi hi' hi0
  change (∫ y, ρ y • fderiv ℝ F (x, y) (0, 1)) = -(∫ y, deriv ρ y • F (x, y)) at H
  rw [H, neg_neg]

/-- The actual normalized horizontal mean has the actual normalized mean
of the physical vertical derivative as its first weak derivative.
No periodicity, weak-equation or Green-identity premise is used. -/
theorem cuspHorizontalMean_weak_verticalDerivative {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (w : ℝ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    (∫ y, deriv ρ y • cuspHorizontalMean w F y) =
      -(∫ y, ρ y • cuspHorizontalMean w (fun p => fderiv ℝ F p (0, 1)) y) := by
  have hd : Continuous (fun p => fderiv ℝ F p (0, 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [cuspHorizontalMean_test_integral hF.continuous (hρ.continuous_deriv (by simp)) hρc.deriv w,
    cuspHorizontalMean_test_integral hd hρ.continuous hρc w]
  simp_rw [cuspPlaneSlice_weak_verticalDerivative hF _ ρ hρ hρc]
  rw [integral_neg, mul_neg]

end
end ArtinMatthews
