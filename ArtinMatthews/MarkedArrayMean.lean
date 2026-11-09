module

public import ArtinMatthews.MarkedBernoulliRealization
public import ArtinMatthews.MarkedArrayEulerModel
public import ArtinMatthews.MarkedEstimateArrayModel


set_option backward.privateInPublic true
@[expose] public section

/-! The main term of the actual array progression estimate is exactly
the finite independent divisor model, including repeated-array moments. -/

namespace ArtinMatthews

open scoped BigOperators

theorem markedWeightedModel_disjoint_union {ι : Type*} [Fintype ι]
    (P S : ι → Finset ℕ) (θ : ℕ → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (hS : ∀ i, S i ⊆ P i) :
    markedWeightedModel (Finset.univ.biUnion P) (Finset.univ.biUnion S) θ =
      ∏ i, markedWeightedModel (P i) (S i) θ := by
  classical
  have hPpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) P :=
    fun _ _ _ _ hij => hdis hij
  have hSpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) S :=
    fun i _ j _ hij => (hdis hij).mono (hS i) (hS j)
  have hDpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i => P i \ S i) :=
    fun _ _ _ _ hij => (hdis hij).mono Finset.sdiff_subset Finset.sdiff_subset
  simp only [markedWeightedModel, Nat.cast_prod, one_div]
  rw [disjoint_bands_residual_union Finset.univ P S hPpair (fun i _ => hS i),
    Finset.prod_biUnion hSpair, Finset.prod_biUnion hDpair,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

theorem markedWeightedModel_arrayDamping {ι : Type*} [Fintype ι]
    (P S : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (i : ι) :
    markedWeightedModel (P i) (S i) (representedArrayDamping Finset.univ P a ρ) =
      markedWeightedModel (P i) (S i) (fun _ => 1 - ρ ^ a i) := by
  classical
  unfold markedWeightedModel
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [representedArrayDamping_on_band Finset.univ P a ρ
    (fun _ _ _ _ hij => hdis hij) (Finset.mem_univ i) (Finset.mem_sdiff.mp hp).1]

theorem representedArrayEulerMean_eq_band_products {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (a : ι → ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    representedArrayEulerMean P V a =
      ∏ i, (∑ t ∈ Fintype.piFinset (fun _ : Fin (a i) => P i),
        (1 / 2 : ℝ) ^ (a i * ((representedChoiceSet t).card - 1)) *
          markedWeightedModel (P i) (representedChoiceSet t)
            (fun _ => 1 - (1 / 2 : ℝ) ^ a i)) / V i ^ a i := by
  classical
  simp_rw [Finset.sum_div]
  rw [Finset.prod_univ_sum]
  unfold representedArrayEulerMean
  apply Finset.sum_congr rfl
  intro t ht
  have hS (i : ι) : representedChoiceSet (t i) ⊆ P i :=
    representedChoiceSet_subset (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht i))
  unfold representedArraySelected representedArrayCoefficient
  rw [markedWeightedModel_disjoint_union P _ _ hdis hS]
  simp_rw [markedWeightedModel_arrayDamping P (fun i => representedChoiceSet (t i)) a (1 / 2) hdis]
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  ring

/-- The Euler main term is a product of the actual finite Bernoulli
moments. The proof realizes every mask by its squarefree prime product. -/
theorem representedArrayEulerMean_eq_bernoulli_moments {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    (V : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    representedArrayEulerMean P V a =
      ∏ i, ∑ A ∈ (P i).powerset, (halfDampedCount A.card / V i) ^ a i *
        bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A := by
  rw [representedArrayEulerMean_eq_band_products P V a hdis]
  exact Finset.prod_congr rfl (fun i _ =>
    represented_band_euler_eq_bernoulli_power (P i) (hP i) (V i) (a i) (ha i))

theorem representedArrayEulerMean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime) (V : ι → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    representedArrayEulerMean P V (fun _ => 1) = independentArrayMean P V := by
  rw [representedArrayEulerMean_eq_bernoulli_moments P hP V _ (fun _ => by decide) hdis,
    independentArrayMean_eq]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [pow_one, bernoulliBandMean, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem representedArrayEulerMean_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime) (V : ι → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    representedArrayEulerMean P V (fun _ => 2) = independentArraySecondMoment P V := by
  rw [representedArrayEulerMean_eq_bernoulli_moments P hP V _ (fun _ => by decide) hdis,
    independentArraySecondMoment_eq]
  rfl

end ArtinMatthews
