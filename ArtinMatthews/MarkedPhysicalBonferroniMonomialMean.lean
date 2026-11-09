module

public import ArtinMatthews.MarkedPhysicalLineLossProjection


set_option backward.privateInPublic true
@[expose] public section

/-! A proved independent-line upper bound for each actual selected
Bonferroni monomial, with the true SL2 residue average on the left. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalLineTuple_card (S : ℕ) :
    Fintype.card (MarkedRootLineTuple S) = ∏ p : S.primeFactors,((p:ℕ)+1) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro p _
  rw [Fintype.card_eq_nat_card,markedProjectiveLine_card]

theorem markedPhysicalLineBonferroniMonomial_mean_le
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T ⊆ S.primeFactors) (hno : ∀ p ∈ T,p ∉ markedPhysicalPathUsedPrimes I a) :
    (∑ ell : MarkedRootLineTuple S,markedPhysicalLineBonferroniMonomial ell I a r z hz T)/
      (Fintype.card (MarkedRootLineTuple S):ℝ) ≤
      ∏ p ∈ T,(∑ v ∈ I,(1-r v))/((p:ℝ)+1) := by
  let U : Finset S.primeFactors := Finset.univ.filter (fun p => (p:ℕ) ∈ T)
  have hp (ell : MarkedRootLineTuple S) :
      (∏ p ∈ T,markedPhysicalLinePrimeLoss ell I a r z hz p) =
      ∏ p ∈ U,markedFiniteLineLoss I r (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v)) (ell p) := by
    calc
      _ = ∏ p : S.primeFactors,if (p:ℕ) ∈ T then markedPhysicalLinePrimeLoss ell I a r z hz p else 1 :=
        (marked_finset_subtype_product S.primeFactors T hT _).symm
      _ = ∏ p ∈ U,markedPhysicalLinePrimeLoss ell I a r z hz p := by
        dsimp only [U]
        rw [Finset.prod_filter]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        exact markedPhysicalLinePrimeLoss_eq_finite ell I a r z hz p (hno _ (Finset.mem_filter.mp hp).2)
  have hμ : (∏ p ∈ U,(∑ v ∈ I,(1-r v))/((p:ℝ)+1)) = ∏ p ∈ T,(∑ v ∈ I,(1-r v))/((p:ℝ)+1) := by
    dsimp only [U]
    rw [Finset.prod_filter]
    exact marked_finset_subtype_product S.primeFactors T hT
      (fun p : ℕ => (∑ v ∈ I,(1-r v))/((p:ℝ)+1))
  calc
    _ ≤ (∑ ell : MarkedRootLineTuple S,∏ p ∈ T,markedPhysicalLinePrimeLoss ell I a r z hz p)/
        (Fintype.card (MarkedRootLineTuple S):ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ell _ =>
        markedPhysicalLineBonferroniMonomial_le_loss_product ell I a r hr z hz T)) (Nat.cast_nonneg _)
    _ = (∑ ell : MarkedRootLineTuple S,∏ p ∈ U,
        markedFiniteLineLoss I r (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v)) (ell p))/
          (Fintype.card (MarkedRootLineTuple S):ℝ) := by simp_rw [hp]
    _ ≤ _ := (markedPhysicalLineLossProduct_mean_le U I r hr z hz).trans_eq hμ

theorem markedPhysicalResidueBonferroniMonomial_mean_le
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ} [NeZero S]
    (hS : Squarefree S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T ⊆ S.primeFactors) (hno : ∀ p ∈ T,p ∉ markedPhysicalPathUsedPrimes I a) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),markedPhysicalResidueBonferroniMonomial hS g I a r z hz T)/
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ) ≤
      ∏ p ∈ T,(∑ v ∈ I,(1-r v))/((p:ℝ)+1) := by
  rw [markedPhysicalResidueBonferroniMonomial_average,← markedPhysicalLineTuple_card S]
  exact markedPhysicalLineBonferroniMonomial_mean_le I a r hr z hz T hT hno

end ArtinMatthews
