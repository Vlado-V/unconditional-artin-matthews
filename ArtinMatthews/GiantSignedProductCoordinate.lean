module

public import ArtinMatthews.FiniteProductMarginal


set_option backward.privateInPublic true
@[expose] public section

/-! Exact one-coordinate marginals and the finite union bound retain the
original product law, including repeated values. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedProduct_coordinate
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)]
    (w : ∀ i, A i → ℝ) (hw : ∀ i, ∑ a, w i a = 1) (i : I) (F : A i → ℝ) :
    (∑ x : ∀ j, A j, finiteProductMarginalMass w x * F (x i)) =
      ∑ a : A i, w i a * F a := by
  classical
  let E := Equiv.piSplitAt i A
  have hmass (a : A i) (z : ∀ j : {j // j ≠ i}, A j) :
      finiteProductMarginalMass w (E.symm (a, z)) =
        w i a * finiteProductMarginalMass (fun j : {j // j ≠ i} => w j) z := by
    unfold finiteProductMarginalMass
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hi : E.symm (a, z) i = a := by simp [E, Equiv.piSplitAt]
    rw [hi]
    apply congrArg (fun r : ℝ => w i a * r)
    apply Finset.prod_congr rfl
    intro j _
    simp [E, Equiv.piSplitAt, j.property]
  have hval (a : A i) (z : ∀ j : {j // j ≠ i}, A j) : E.symm (a, z) i = a := by
    simp [E, Equiv.piSplitAt]
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [hmass, hval]
  calc
    _ = (w i a * F a) *
        ∑ z : ∀ j : {j // j ≠ i}, A j,
          finiteProductMarginalMass (fun j : {j // j ≠ i} => w j) z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      rw [finiteProductMarginalMass_sum (fun j : {j // j ≠ i} => w j) (fun j => hw j), mul_one]

theorem giantSignedFinite_probability_union
    {E X : Type*} [Fintype E] [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (event : E → X → Prop) :
    (∑ x, w x * (if ∃ e, event e x then 1 else 0 : ℝ)) ≤
      ∑ e, ∑ x, w x * (if event e x then 1 else 0 : ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hw x)
  by_cases h : ∃ e, event e x
  · have hExists := h
    obtain ⟨e, he⟩ := h
    simp only [ite_eq_left hExists]
    exact (by simpa only [ite_eq_left he] using
      (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset E)) =>
        show (0 : ℝ) ≤ if event j x then 1 else 0 by split_ifs <;> norm_num)
        (Finset.mem_univ e)))
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun e _ => by split_ifs <;> norm_num)

end
end ArtinMatthews
