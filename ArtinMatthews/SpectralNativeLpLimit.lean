module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! A pointwise limit of the actual L2 representatives agrees almost
everywhere with their strong L2 limit, on the original measure space. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralLp_two_limit_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → Lp ℂ 2 μ) (u : Lp ℂ 2 μ) (g : α → ℂ)
    (hF : Tendsto F atTop (𝓝 u))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun K => F K x) atTop (𝓝 (g x))) :
    u =ᵐ[μ] g := by
  obtain ⟨ns,hns,hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  filter_upwards [hsub,hg] with x hx hgx
  exact tendsto_nhds_unique hx (hgx.comp hns.tendsto_atTop)

end ArtinMatthews
