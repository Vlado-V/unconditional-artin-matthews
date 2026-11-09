module

public import ArtinMatthews.MarkedPhysicalJointPrimeDamping


set_option backward.privateInPublic true
@[expose] public section

/-! A finite union bound for the literal joint-prime loss. Active flags
are preserved and only lower the loss; no independence is used here. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem marked_one_sub_prod_le_sum {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I,0 ≤ f i ∧ f i ≤ 1) :
    1-(∏ i ∈ I,f i) ≤ ∑ i ∈ I,(1-f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,sub_self,le_refl]
  | @insert a I ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfi (i : ι) (hi : i ∈ I) := hf i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ I,f i) ≤ 1 := Finset.prod_le_one₀ (fun i hi => (hfi i hi).1) (fun i hi => (hfi i hi).2)
    have hih := ih hfi
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr hfa.2) (sub_nonneg.mpr hprod)]

theorem markedPhysicalPrimeVisitFactor_loss_le (active : Finset ℕ) {r : ℝ}
    (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) (u p : ℕ) :
    1-markedPhysicalPrimeVisitFactor active r u p ≤ (1-r)*(if p ∣ u then (1:ℝ) else 0) := by
  classical
  unfold markedPhysicalPrimeVisitFactor
  split_ifs <;> simp_all

theorem markedPhysicalInactivePrimeLoss_le_hits
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (p : ℕ) :
    markedPhysicalInactivePrimeLoss I a r u p ≤
      ∑ v ∈ I,(1-r v)*(if p ∣ u v then (1:ℝ) else 0) := by
  classical
  apply (marked_one_sub_prod_le_sum I _ (fun v hv =>
    markedPhysicalPrimeVisitFactor_mem_unitInterval _ (hr v hv).1 (hr v hv).2 _ _)).trans
  exact Finset.sum_le_sum (fun v hv => markedPhysicalPrimeVisitFactor_loss_le _ (hr v hv).1 (hr v hv).2 _ _)

end ArtinMatthews
