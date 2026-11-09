module

public import ArtinMatthews.MarkedPhysicalBonferroniCRT


set_option backward.privateInPublic true
@[expose] public section

/-! Performed finite independent-product averages. These identities will
be applied to the actual projective-line fibers, not assumed as a law. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable

theorem marked_finite_pi_product_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i,Fintype (F i)] (f : ∀ i,F i → ℝ) :
    (∑ x : ∀ i,F i,∏ i,f i (x i))/(Fintype.card (∀ i,F i):ℝ) =
      ∏ i,(∑ y : F i,f i y)/(Fintype.card (F i):ℝ) := by
  rw [← Fintype.prod_sum f,Fintype.card_pi,Nat.cast_prod,← Finset.prod_div_distrib]

theorem marked_finite_pi_product_mean_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i,Fintype (F i)] [∀ i,Nonempty (F i)]
    (T : Finset ι) (f : ∀ i,F i → ℝ) :
    (∑ x : ∀ i,F i,∏ i ∈ T,f i (x i))/(Fintype.card (∀ i,F i):ℝ) =
      ∏ i ∈ T,(∑ y : F i,f i y)/(Fintype.card (F i):ℝ) := by
  classical
  have hp (x : ∀ i,F i) : (∏ i,if i ∈ T then f i (x i) else 1) = ∏ i ∈ T,f i (x i) := by
    simp only [Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.prod_const_one,mul_one]
  have hm (i : ι) : (∑ y : F i,if i ∈ T then f i y else 1)/(Fintype.card (F i):ℝ) =
      if i ∈ T then (∑ y : F i,f i y)/(Fintype.card (F i):ℝ) else 1 := by
    by_cases hi : i ∈ T
    · simp only [ite_eq_left hi]
    · simp only [ite_eq_right hi,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  have h := marked_finite_pi_product_mean F (fun i y => if i ∈ T then f i y else 1)
  simp_rw [hp,hm] at h
  simpa only [Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.prod_const_one,mul_one] using h

theorem marked_finset_subtype_product {ι : Type*} [DecidableEq ι] (S T : Finset ι) (hT : T ⊆ S) (f : ι → ℝ) :
    (∏ p : S,if p.1 ∈ T then f p.1 else 1) = ∏ p ∈ T,f p := by
  classical
  rw [Finset.prod_coe_sort S (fun p : ι => if p ∈ T then f p else 1)]
  simp only [Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hT,
    Finset.prod_const_one,mul_one]

theorem marked_finite_projective_product_mean_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i,Field (F i)] [∀ i,Fintype (F i)] [∀ i,DecidableEq (F i)]
    (T : Finset ι) (f : ∀ i,ℙ (F i) (Fin 2 → F i) → ℝ) :
    (∑ x : ∀ i,ℙ (F i) (Fin 2 → F i),∏ i ∈ T,f i (x i))/
      (Fintype.card (∀ i,ℙ (F i) (Fin 2 → F i)):ℝ) =
      ∏ i ∈ T,(∑ y : ℙ (F i) (Fin 2 → F i),f i y)/(Fintype.card (ℙ (F i) (Fin 2 → F i)):ℝ) := by
  let : ∀ i,Nonempty (ℙ (F i) (Fin 2 → F i)) := fun i => ⟨markedVerticalProjectiveLine (F i)⟩
  exact marked_finite_pi_product_mean_on _ T f

end ArtinMatthews
