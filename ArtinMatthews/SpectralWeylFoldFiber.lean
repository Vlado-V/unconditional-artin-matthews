module

public import ArtinMatthews.SpectralWeylFoldSubstitution


set_option backward.privateInPublic true
@[expose] public section

/-! Transport of the actual height fiber, its norm integral, and its
absolute integrability to the fixed fold interval. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

private theorem spectral_fold_cut_integrable_iff {E : Type*} [NormedAddCommGroup E]
    {B : ℝ} (F : ℝ → E) (hzero : ∀ z : ℝ, B ≤ z → F z = 0) :
    IntegrableOn F (Ioi (0 : ℝ)) ↔ IntegrableOn F (Ioo 0 B) := by
  have he : EqOn F ((Ioo (0 : ℝ) B).indicator F) (Ioi (0 : ℝ)) := by
    intro z hz
    by_cases hz' : z ∈ Ioo (0 : ℝ) B
    · rw [indicator_of_mem hz']
    · rw [indicator_of_notMem hz']
      exact hzero z (le_of_not_gt (fun hlt => hz' ⟨hz,hlt⟩))
  apply (integrableOn_congr_fun he measurableSet_Ioi).trans
  change Integrable ((Ioo (0 : ℝ) B).indicator F) (volume.restrict (Ioi (0 : ℝ))) ↔
    Integrable F (volume.restrict (Ioo (0 : ℝ) B))
  rw [integrable_indicator_iff measurableSet_Ioo,IntegrableOn,
    Measure.restrict_restrict_of_subset Ioo_subset_Ioi_self]

private theorem spectral_fold_cut_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (F : ℝ → E) (hzero : ∀ z : ℝ, B ≤ z → F z = 0) :
    (∫ z in Ioi (0 : ℝ), F z) = ∫ z in Ioo (0 : ℝ) B, F z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
  intro z hz
  exact hzero z (le_of_not_gt (fun hlt => hz.2 ⟨hz.1,hlt⟩))

theorem spectralWeylPhysicalFiber_fold_integrable_iff {X x : ℝ} (hX : 0 < X) (hx : 0 < x)
    (s t : ℝ) (f g : ℝ → ℂ) :
    Integrable (fun z : ℝ => spectralWeylPhysicalIntegrand s t f g ((x,z),X)) spectralKLPhysicalMeasure ↔
      IntegrableOn (fun u : ℝ => spectralWeylFoldDensity s t f g X (x,u)) (Ioo (0 : ℝ) 1) := by
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_complex_integrable_iff _ _
    (by fun_prop) (fun z hz => inv_nonneg.mpr hz.le)]
  let B := X^2/(4*x)
  let F : ℝ → ℂ := fun z => ((z⁻¹ : ℝ) : ℂ)*spectralWeylPhysicalIntegrand s t f g ((x,z),X)
  have hB : 0 < B := by dsimp [B]; positivity
  have hzero (z : ℝ) (hz : B ≤ z) : F z = 0 := by
    simp only [F,spectralWeylPhysicalIntegrand,spectralWeylDimensionlessKernel_zero_of_cut hX hx hz s t,
      Complex.ofReal_zero,zero_mul,mul_zero]
  apply (spectral_fold_cut_integrable_iff F hzero).trans
  apply (spectralWeylFoldHeight_integrable hB F).trans
  apply integrableOn_congr_fun _ measurableSet_Ioo
  intro u hu
  simpa only [F,Complex.ofReal_inv] using spectralWeylFoldDensity_jacobian hX hx hu s t f g

theorem spectralWeylPhysicalFiber_fold_integral {X x : ℝ} (hX : 0 < X) (hx : 0 < x)
    (s t : ℝ) (f g : ℝ → ℂ) :
    (∫ z : ℝ, spectralWeylPhysicalIntegrand s t f g ((x,z),X) ∂spectralKLPhysicalMeasure) =
      ∫ u in Ioo (0 : ℝ) 1, spectralWeylFoldDensity s t f g X (x,u) := by
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_complex_integral _ _
    (by fun_prop) (fun z hz => inv_nonneg.mpr hz.le)]
  let B := X^2/(4*x)
  let F : ℝ → ℂ := fun z => ((z⁻¹ : ℝ) : ℂ)*spectralWeylPhysicalIntegrand s t f g ((x,z),X)
  have hB : 0 < B := by dsimp [B]; positivity
  have hzero (z : ℝ) (hz : B ≤ z) : F z = 0 := by
    simp only [F,spectralWeylPhysicalIntegrand,spectralWeylDimensionlessKernel_zero_of_cut hX hx hz s t,
      Complex.ofReal_zero,zero_mul,mul_zero]
  rw [spectral_fold_cut_integral F hzero,spectralWeylFoldHeight_integral hB F]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  simpa only [F,Complex.ofReal_inv] using spectralWeylFoldDensity_jacobian hX hx hu s t f g

theorem spectralWeylPhysicalFiber_fold_norm_integral {X x : ℝ} (hX : 0 < X) (hx : 0 < x)
    (s t : ℝ) (f g : ℝ → ℂ) :
    (∫ z : ℝ, ‖spectralWeylPhysicalIntegrand s t f g ((x,z),X)‖ ∂spectralKLPhysicalMeasure) =
      ∫ u in Ioo (0 : ℝ) 1, ‖spectralWeylFoldDensity s t f g X (x,u)‖ := by
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_integral _ _
    (by fun_prop) (fun z hz => inv_nonneg.mpr hz.le)]
  let B := X^2/(4*x)
  let F : ℝ → ℝ := fun z => z⁻¹*‖spectralWeylPhysicalIntegrand s t f g ((x,z),X)‖
  have hB : 0 < B := by dsimp [B]; positivity
  have hzero (z : ℝ) (hz : B ≤ z) : F z = 0 := by
    simp only [F,spectralWeylPhysicalIntegrand,spectralWeylDimensionlessKernel_zero_of_cut hX hx hz s t,
      Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
  rw [spectral_fold_cut_integral F hzero,spectralWeylFoldHeight_integral hB F]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hz : 0 < spectralWeylFoldHeight B u := by
    have hmem : spectralWeylFoldHeight B u ∈ spectralWeylFoldHeight B '' Ioo (0 : ℝ) 1 := ⟨u,hu,rfl⟩
    rw [spectralWeylFoldHeight_image hB] at hmem
    exact hmem.1
  have h := congrArg (fun w : ℂ => ‖w‖) (spectralWeylFoldDensity_jacobian hX hx hu s t f g)
  change ‖(2*B*u : ℝ) • (( (spectralWeylFoldHeight B u)⁻¹ : ℂ)*
    spectralWeylPhysicalIntegrand s t f g ((x,spectralWeylFoldHeight B u),X))‖ = _ at h
  rw [← Complex.ofReal_inv] at h
  simpa only [F,norm_smul,Real.norm_of_nonneg (mul_pos (mul_pos two_pos hB) hu.1).le,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hz.le),smul_eq_mul] using h

end ArtinMatthews
