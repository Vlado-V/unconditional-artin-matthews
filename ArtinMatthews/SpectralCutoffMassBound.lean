module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine cutoff removes only the mass outside its plateau. -/

open Set MeasureTheory Filter

namespace ArtinMatthews

theorem cutoff_residual_mass_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F a : α → ℂ) {T : Set α} (hT : MeasurableSet T)
    (hF : Integrable (fun x => ‖F x‖^2) μ)
    (hmF : AEStronglyMeasurable F μ) (hma : AEStronglyMeasurable a μ)
    (hres : ∀ x, ‖1-a x‖ ≤ 1)
    (hplateau : ∀ᵐ x ∂μ, x ∉ T → a x = 1) :
    Integrable (fun x => ‖(1-a x)*F x‖^2) μ ∧
      (∫ x, ‖(1-a x)*F x‖^2 ∂μ) ≤ ∫ x in T, ‖F x‖^2 ∂μ := by
  classical
  have hi := hF.indicator hT
  have hm : AEStronglyMeasurable (fun x => ‖(1-a x)*F x‖^2) μ :=
    ((aestronglyMeasurable_const.sub hma).mul hmF).norm.pow 2
  have hle : ∀ᵐ x ∂μ, ‖(1-a x)*F x‖^2 ≤ T.indicator (fun x => ‖F x‖^2) x := by
    filter_upwards [hplateau] with x hx
    by_cases ht : x ∈ T
    · rw [indicator_of_mem ht,norm_mul,mul_pow]
      have hh := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr (hres x)
      simpa only [one_pow,one_mul] using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖F x‖)
    · rw [indicator_of_notMem ht,hx ht,sub_self,zero_mul,norm_zero,zero_pow two_ne_zero]
  have hir : Integrable (fun x => ‖(1-a x)*F x‖^2) μ := by
    apply hi.mono' hm
    filter_upwards [hle] with x hx
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  refine ⟨hir,?_⟩
  rw [← integral_indicator hT]
  exact integral_mono_ae hir hi hle

end ArtinMatthews
