module

public import ArtinMatthews.MarkedArrayExpansion
public import ArtinMatthews.MarkedProgressionWeightedModel


set_option backward.privateInPublic true
@[expose] public section

/-! The exact represented-sum Euler mean and normalized coefficients used
when transferring the actual marking weights to progressions. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def representedArraySelected {ι : Type*} [Fintype ι] {a : ι → ℕ}
    (t : (i : ι) → Fin (a i) → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => representedChoiceSet (t i))

noncomputable def representedArrayCoefficient {ι : Type*} [Fintype ι]
    (V : ι → ℝ) (a : ι → ℕ) (t : (i : ι) → Fin (a i) → ℕ) : ℝ :=
  (∏ i, (1 / 2 : ℝ) ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
    (∏ i, V i ^ a i)

noncomputable def representedArrayEulerMean {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (a : ι → ℕ) : ℝ :=
  ∑ t ∈ representedArrayChoices P a, representedArrayCoefficient V a t *
    markedWeightedModel (Finset.univ.biUnion P) (representedArraySelected t)
      (representedArrayDamping Finset.univ P a (1 / 2))

/-- The actual arithmetic array is precisely the normalized finite family
of selected residuals whose Euler mean was defined above. -/
theorem bandWeight_product_powers_eq_normalized_residual_sum {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (u : ℕ) :
    (∏ i, (bandWeight (P i) (V i) u) ^ a i) =
      ∑ t ∈ representedArrayChoices P a, representedArrayCoefficient V a t *
        markedWeightedResidual (Finset.univ.biUnion P) (representedArraySelected t)
          (representedArrayDamping Finset.univ P a (1 / 2)) u := by
  classical
  rw [bandWeight_product_powers_eq_union_residual_sum P V a ha hdis u, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  unfold representedArrayCoefficient representedArraySelected
  ring

end ArtinMatthews
