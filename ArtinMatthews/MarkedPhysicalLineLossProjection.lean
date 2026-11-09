module

public import ArtinMatthews.MarkedPhysicalBonferroniCRT
public import ArtinMatthews.MarkedPhysicalPrimeLossMean
public import ArtinMatthews.MarkedFiniteProductAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Actual line-tuple monomials project to their selected one-prime
losses. Used-prime factors are dropped only in this nonnegative error
bound; the exact main-term factors remain in the original monomial. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable

theorem markedPhysicalLinePrimePathFactor_mem_unitInterval
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (ell : MarkedRootLineTuple S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) :
    0 ≤ markedPhysicalLinePrimePathFactor ell I a r z hz p ∧ markedPhysicalLinePrimePathFactor ell I a r z hz p ≤ 1 := by
  have hf (v : ι) (hv : v ∈ I) :
      0 ≤ markedPhysicalLineVisitFactor ell (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p ∧
      markedPhysicalLineVisitFactor ell (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p ≤ 1 := by
    have hh := hr v hv
    unfold markedPhysicalLineVisitFactor
    split_ifs <;> constructor <;> linarith
  exact ⟨Finset.prod_nonneg (fun v hv => (hf v hv).1),
    Finset.prod_le_one₀ (fun v hv => (hf v hv).1) (fun v hv => (hf v hv).2)⟩

theorem markedPhysicalLineBonferroniMonomial_le_loss_product
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (ell : MarkedRootLineTuple S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) :
    markedPhysicalLineBonferroniMonomial ell I a r z hz T ≤ ∏ p ∈ T,markedPhysicalLinePrimeLoss ell I a r z hz p := by
  have hf (p : ℕ) := markedPhysicalLinePrimePathFactor_mem_unitInterval ell I a r hr z hz p
  have hu : (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalLinePrimePathFactor ell I a r z hz p) ≤ 1 :=
    Finset.prod_le_one₀ (fun p _ => (hf p).1) (fun p _ => (hf p).2)
  exact mul_le_of_le_one_left
    (Finset.prod_nonneg (fun p _ => sub_nonneg.mpr (hf p).2)) hu

theorem markedPhysicalLinePrimeLoss_eq_finite
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (ell : MarkedRootLineTuple S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : S.primeFactors)
    (hp : (p:ℕ) ∉ markedPhysicalPathUsedPrimes I a) :
    markedPhysicalLinePrimeLoss ell I a r z hz p =
      markedFiniteLineLoss I r (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v)) (ell p) := by
  unfold markedPhysicalLinePrimeLoss markedPhysicalLinePrimePathFactor markedFiniteLineLoss
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have hn : (p:ℕ) ∉ markedPhysicalActivePrimes (a v) := fun hm => hp (Finset.mem_biUnion.mpr ⟨v,hv,hm⟩)
  simp only [markedPhysicalLineVisitFactor,ite_eq_right hn,markedPhysicalLineTupleHit,dite_eq_left p.2]

theorem markedPhysicalLineLossProduct_mean_le {ι : Type*} {S : ℕ}
    (U : Finset S.primeFactors) (I : Finset ι) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) :
    (∑ ell : MarkedRootLineTuple S,∏ p ∈ U,
      markedFiniteLineLoss I r (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v)) (ell p))/
        (Fintype.card (MarkedRootLineTuple S):ℝ) ≤
      ∏ p ∈ U,(∑ v ∈ I,(1-r v))/((p:ℝ)+1) := by
  have hmean := marked_finite_projective_product_mean_on
    (fun p : S.primeFactors => ZMod (p:ℕ)) U
    (fun p ell => markedFiniteLineLoss I r (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v)) ell)
  rw [hmean]
  apply Finset.prod_le_prod₀
  · intro p _
    exact div_nonneg (Finset.sum_nonneg (fun ell _ => (markedFiniteLineLoss_mem_unitInterval I r hr _ ell).1))
      (Nat.cast_nonneg _)
  · intro p _
    simpa only [Fintype.card_eq_nat_card,markedProjectiveLine_card,Nat.cast_add,Nat.cast_one] using
      markedFiniteLineLoss_mean_le I r hr (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v))

end ArtinMatthews
