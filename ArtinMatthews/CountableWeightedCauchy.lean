module

public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy for an actual countable complex row, obtained from
its finite sums with all three convergences retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem finiteWeightedCauchy {ι : Type*} (s : Finset ι)
    (c f : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ‖∑ i ∈ s, c i * f i‖ ^ 2 ≤
      (∑ i ∈ s, ‖c i‖ * w i) * (∑ i ∈ s, ‖c i‖ * ‖f i‖ ^ 2 / w i) := by
  have ht : ‖∑ i ∈ s, c i * f i‖ ≤ ∑ i ∈ s, ‖c i‖ * ‖f i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => c i * f i)
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (norm_nonneg _) (hw i).le
  · intro i _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hw i).le
  · intro i _
    exact le_of_eq (by field_simp [(hw i).ne'])

theorem countableWeightedCauchy {ι : Type*} (c f : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hf : Summable (fun i => c i * f i))
    (hcw : Summable (fun i => ‖c i‖ * w i))
    (hcf : Summable (fun i => ‖c i‖ * ‖f i‖ ^ 2 / w i)) :
    ‖∑' i, c i * f i‖ ^ 2 ≤
      (∑' i, ‖c i‖ * w i) * (∑' i, ‖c i‖ * ‖f i‖ ^ 2 / w i) := by
  exact le_of_tendsto_of_tendsto (hf.hasSum.norm.pow 2)
    (Filter.Tendsto.mul hcw.hasSum hcf.hasSum)
    (Filter.Eventually.of_forall fun s => finiteWeightedCauchy s c f w hw)

end
end ArtinMatthews
