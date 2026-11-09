module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute summability and exact factorization for products over finitely
many independent coordinates. No Gaussian-specific premise is required. -/
set_option maxHeartbeats 800000
noncomputable section
namespace ArtinMatthews.GaussianCoordinateProduct
open scoped BigOperators Classical

private def coordinateProductProperty
    (A : Type*) [NormedCommRing A] (ι : Type*) (β : Type*) [Fintype β] : Prop :=
  ∀ f : β → ι → A, (∀ i, Summable (fun n => ‖f i n‖)) →
    Summable (fun x : β → ι => ‖∏ i, f i (x i)‖) ∧
      (∑' x : β → ι, ∏ i, f i (x i)) = ∏ i, ∑' n : ι, f i n

private theorem coordinateProductProperty_equiv
    {A : Type*} [NormedCommRing A] {ι α γ : Type*} [Fintype α] [Fintype γ]
    (e : α ≃ γ) (ih : coordinateProductProperty A ι α) :
    coordinateProductProperty A ι γ := by
  intro f hf
  let E : (α → ι) ≃ (γ → ι) := Equiv.arrowCongr e (Equiv.refl ι)
  have hp (x : α → ι) : (∏ i : γ, f i (E x i)) = ∏ i : α, f (e i) (x i) := by
    rw [← e.prod_comp]
    simp [E, Equiv.arrowCongr_apply]
  have h := ih (fun i => f (e i)) (fun i => hf (e i))
  constructor
  · apply E.summable_iff.mp
    simpa only [Function.comp_def, hp] using h.1
  · rw [← E.tsum_eq (fun x : γ → ι => ∏ i, f i (x i))]
    simp_rw [hp]
    rw [h.2]
    exact e.prod_comp (fun i => ∑' n : ι, f i n)

private theorem coordinateProductProperty_empty
    (A : Type*) [NormedCommRing A] (ι : Type*) : coordinateProductProperty A ι PEmpty := by
  intro f _
  constructor
  · exact (hasSum_fintype _).summable
  · simp

private theorem coordinateProductProperty_option
    {A : Type*} [NormedCommRing A] [CompleteSpace A] {ι α : Type*} [Fintype α]
    (ih : coordinateProductProperty A ι α) : coordinateProductProperty A ι (Option α) := by
  intro f hf
  let E : (ι × (α → ι)) ≃ (Option α → ι) :=
    (Equiv.piOptionEquivProd (α := α) (β := fun _ => ι)).symm
  have hp (x : ι × (α → ι)) :
      (∏ i : Option α, f i (E x i)) = f none x.1 * ∏ i : α, f (some i) (x.2 i) := by
    simp [Fintype.prod_option, E, Equiv.piOptionEquivProd_symm_apply]
  have h := ih (fun i => f (some i)) (fun i => hf (some i))
  constructor
  · apply E.summable_iff.mp
    simpa only [Function.comp_def, hp] using (hf none).mul_norm h.1
  · rw [← E.tsum_eq (fun x : Option α → ι => ∏ i, f i (x i))]
    simp_rw [hp]
    rw [← tsum_mul_tsum_of_summable_norm (hf none) h.1, h.2, Fintype.prod_option]

/-- A finite product of absolutely summable coordinate functions is absolutely
summable on the full product index, and its sum is the product of the sums. -/
theorem summable_norm_and_tsum_prod
    {A : Type*} [NormedCommRing A] [CompleteSpace A] {ι : Type*}
    (β : Type*) [Fintype β] (f : β → ι → A)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun x : β → ι => ‖∏ i, f i (x i)‖) ∧
      (∑' x : β → ι, ∏ i, f i (x i)) = ∏ i, ∑' n : ι, f i n := by
  have h : coordinateProductProperty A ι β :=
    Fintype.induction_empty_option
      (P := coordinateProductProperty A ι)
      (fun α γ _ e ih => by
        let := Fintype.ofEquiv γ e.symm
        exact coordinateProductProperty_equiv e ih)
      (coordinateProductProperty_empty A ι)
      (fun _ _ ih => coordinateProductProperty_option ih) β
  exact h f hf

/-- Complex-valued finite coordinate products are absolutely summable. -/
theorem complex_summable_norm_prod {β : Type*} [Fintype β] (f : β → ℤ → ℂ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun x : β → ℤ => ‖∏ i, f i (x i)‖) :=
  (summable_norm_and_tsum_prod β f hf).1

/-- Exact factorization of an absolutely summable complex coordinate product. -/
theorem complex_tsum_prod {β : Type*} [Fintype β] (f : β → ℤ → ℂ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    (∑' x : β → ℤ, ∏ i, f i (x i)) = ∏ i, ∑' n : ℤ, f i n :=
  (summable_norm_and_tsum_prod β f hf).2

/-- The complex coordinate product itself is summable. -/
theorem complex_summable_prod {β : Type*} [Fintype β] (f : β → ℤ → ℂ)
    (hf : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun x : β → ℤ => ∏ i, f i (x i)) :=
  (complex_summable_norm_prod f hf).of_norm

/-- Real nonnegative coordinate products are summable and factor exactly. -/
theorem real_nonnegative_summable_and_tsum_prod {β : Type*} [Fintype β] (f : β → ℤ → ℝ)
    (hf : ∀ i, Summable (f i)) (hnonneg : ∀ i n, 0 ≤ f i n) :
    Summable (fun x : β → ℤ => ∏ i, f i (x i)) ∧
      (∑' x : β → ℤ, ∏ i, f i (x i)) = ∏ i, ∑' n : ℤ, f i n := by
  have hnorm (i) : Summable (fun n => ‖f i n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg i _)] using hf i
  have h := summable_norm_and_tsum_prod β f hnorm
  exact ⟨h.1.of_norm, h.2⟩

end ArtinMatthews.GaussianCoordinateProduct
