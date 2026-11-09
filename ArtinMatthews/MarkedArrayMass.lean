module

public import ArtinMatthews.MarkedArrayExpansion
public import ArtinMatthews.MarkedRepresentedMass


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocal masses of represented unions factor across genuinely
disjoint bands, with repeated selections kept as ordered tuples. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def representedTupleReciprocalMass (P : Finset ℕ) (a : ℕ) (ρ : ℝ) : ℝ :=
  ∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
    ρ ^ (a * ((representedChoiceSet t).card - 1)) /
      ∏ p ∈ representedChoiceSet t, (p : ℝ)

theorem represented_union_reciprocal_eq_product {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (t : (i : ι) → Fin (a i) → ℕ) (ht : t ∈ representedArrayChoices P a) :
    (∏ i, ρ ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
        (∏ p ∈ Finset.univ.biUnion (fun i => representedChoiceSet (t i)), (p : ℝ)) =
      ∏ i, ρ ^ (a i * ((representedChoiceSet (t i)).card - 1)) /
        (∏ p ∈ representedChoiceSet (t i), (p : ℝ)) := by
  classical
  have htp : ∀ i j, t i j ∈ P i := fun i =>
    Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht i)
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι))
      (fun i => representedChoiceSet (t i)) := by
    intro i _ j _ hij
    exact (hdis hij).mono (representedChoiceSet_subset (htp i))
      (representedChoiceSet_subset (htp j))
  rw [Finset.prod_biUnion hpair, Finset.prod_div_distrib]

/-- Exact factorization of the mass multiplying the Bonferroni tail and
the local coprimality loss in the actual array expansion. -/
theorem represented_array_reciprocal_mass_factor {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    (∑ t ∈ representedArrayChoices P a,
      (∏ i, ρ ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
        (∏ p ∈ Finset.univ.biUnion (fun i => representedChoiceSet (t i)), (p : ℝ))) =
      ∏ i, representedTupleReciprocalMass (P i) (a i) ρ := by
  classical
  simp_rw [representedTupleReciprocalMass]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact represented_union_reciprocal_eq_product P a ρ hdis t ht

theorem representedChoiceSet_one (t : Fin 1 → ℕ) :
    representedChoiceSet t = {t 0} := by
  ext p
  simp [representedChoiceSet]

theorem representedTupleReciprocalMass_one (P : Finset ℕ) (ρ : ℝ) :
    representedTupleReciprocalMass P 1 ρ = bandReciprocalMass P := by
  classical
  unfold representedTupleReciprocalMass bandReciprocalMass
  apply Finset.sum_bij (fun t _ => t 0)
  · intro t ht
    exact Fintype.mem_piFinset.mp ht 0
  · intro t ht s hs hts
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa [hj] using hts
  · intro p hp
    exact ⟨fun _ => p, Fintype.mem_piFinset.mpr (fun _ => hp), rfl⟩
  · intro t ht
    simp [representedChoiceSet_one]

theorem representedChoiceSet_two (t : Fin 2 → ℕ) :
    representedChoiceSet t = {t 0, t 1} := by
  ext p
  simp [representedChoiceSet, Fin.exists_fin_two, eq_comm]

theorem representedTupleReciprocalMass_two (P : Finset ℕ) (ρ : ℝ) :
    representedTupleReciprocalMass P 2 ρ = representedPairReciprocalMass P ρ := by
  classical
  unfold representedTupleReciprocalMass representedPairReciprocalMass
  rw [← Finset.sum_product (f := fun pq : ℕ × ℕ =>
    ρ ^ (2 * (({pq.1, pq.2} : Finset ℕ).card - 1)) /
      ∏ r ∈ ({pq.1, pq.2} : Finset ℕ), (r : ℝ))]
  apply Finset.sum_bij (fun t _ => (t 0, t 1))
  · intro t ht
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp ht 0, Fintype.mem_piFinset.mp ht 1⟩
  · intro t ht s hs hts
    funext j
    fin_cases j
    · exact congrArg Prod.fst hts
    · exact congrArg Prod.snd hts
  · intro pq hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    refine ⟨![pq.1, pq.2], Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      fin_cases j <;> assumption
    · rfl
  · intro t ht
    simp only [representedChoiceSet_two]

end ArtinMatthews
