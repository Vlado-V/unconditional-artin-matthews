module

public import ArtinMatthews.MarkedPhysicalCanonicalWeightSum


set_option backward.privateInPublic true
@[expose] public section

/-! A finite nonnegative target-extension inequality, factored separately
so physical coefficient definitions need not unfold in finite algebra. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysical_finite_block_le {ι κ : Type*} [Fintype ι]
    (s : ι → Finset κ) (t : Finset κ) (F : ι → κ → ℂ) (w : ι → κ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i z, z ∈ s i → ‖F i z‖ ≤ C*(if z ∈ t then w i z else 0))
    (hw : ∀ i z, z ∈ t → 0 ≤ w i z) :
    (∑ i, ∑ z ∈ s i, ‖F i z‖) ≤ C * ∑ i, ∑ z ∈ t, w i z := by
  calc
    _ ≤ ∑ i, ∑ z ∈ s i, C*(if z ∈ t then w i z else 0) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun z hz => hF i z hz)
    _ = C * ∑ i, ∑ z ∈ s i, if z ∈ t then w i z else 0 := by simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun i _ => markedPhysical_sum_indicator_le (s i) t (w i) (hw i))

end ArtinMatthews
