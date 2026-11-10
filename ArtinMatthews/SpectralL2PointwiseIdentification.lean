module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Strong actual L2 limits and genuine pointwise limits identify the same
almost-everywhere representative by a proved subsequence argument. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Filter Topology

theorem spectralL2_ae_eq_of_tendsto_pointwise {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : ℕ → Lp ℂ 2 μ) (U : Lp ℂ 2 μ) (f : ℕ → α → ℂ) (F : α → ℂ)
    (hU : Tendsto u atTop (𝓝 U)) (hu : ∀ n, u n =ᵐ[μ] f n)
    (hF : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) : U =ᵐ[μ] F := by
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hU).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr hu
  filter_upwards [hae,hall,hF] with x hx he hf
  have ht := hf.comp hns.tendsto_atTop
  have hEq : (fun n => (u (ns n)) x)=(fun n => f (ns n) x) := funext fun n => he (ns n)
  simp only [Function.comp_def] at ht
  rw [← hEq] at ht
  exact tendsto_nhds_unique hx ht

end
end ArtinMatthews
