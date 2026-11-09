module

public import ArtinMatthews.GiantCandidateModelHitCoordinates
public import ArtinMatthews.GiantCandidateModelRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! In the independent carrier, a specified distinct pair can be the
unique predecessor and product hits, with every other prime unhit. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateModelOneEachCoordinate {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (a b p : giantCandidateSelectionPrimes G) :
    Finset (Fin j → ZMod p.val) :=
  if p=a then giantCandidateModelHitCoordinate G hG j p .predecessor
  else if p=b then giantCandidateModelHitCoordinate G hG j p .product
  else giantCandidateModelNoHitCoordinate G hG j p

def giantCandidateModelOneEachEvent {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (a b : giantCandidateSelectionPrimes G) :
    Finset (GiantCandidateModelResidueSpace G j) :=
  Fintype.piFinset (giantCandidateModelOneEachCoordinate G hG j a b)

def giantCandidateModelOneEachPairs {ι : Type*} [Fintype ι] (G : ι → Finset ℕ) :
    Finset (giantCandidateSelectionPrimes G × giantCandidateSelectionPrimes G) :=
  (univ×ˢuniv).filter (fun x => x.1≠x.2)

theorem giantCandidateModelOneEach_residue_iff {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) {j : ℕ} {a b : giantCandidateSelectionPrimes G} (hab : a≠b)
    {t : GiantCandidateModelResidueSpace G j} (ht : t∈giantCandidateModelOneEachEvent G hG j a b)
    (p : giantCandidateSelectionPrimes G) :
    (giantCandidatePrimeResidueHit .predecessor (t p) ↔ p=a) ∧
      (giantCandidatePrimeResidueHit .product (t p) ↔ p=b) := by
  let _ : Fact p.val.Prime := ⟨giantCandidateModelPrime_prime G hG p⟩
  have hp := Fintype.mem_piFinset.mp ht p
  unfold giantCandidateModelOneEachCoordinate at hp
  by_cases ha : p=a
  · rw [ite_eq_left ha] at hp
    have h₁ := (mem_giantCandidateModelHitCoordinate G hG j p .predecessor (t p)).mp hp
    have h₂ : ¬giantCandidatePrimeResidueHit .product (t p) := fun h => one_ne_zero (h₁.symm.trans h)
    exact ⟨iff_of_true h₁ ha,iff_of_false h₂ (fun h => hab (ha.symm.trans h))⟩
  · rw [ite_eq_right ha] at hp
    by_cases hb : p=b
    · rw [ite_eq_left hb] at hp
      have h₂ := (mem_giantCandidateModelHitCoordinate G hG j p .product (t p)).mp hp
      have h₁ : ¬giantCandidatePrimeResidueHit .predecessor (t p) := fun h => one_ne_zero (h.symm.trans h₂)
      exact ⟨iff_of_false h₁ ha,iff_of_true h₂ hb⟩
    · rw [ite_eq_right hb] at hp
      have h := (mem_giantCandidateModelNoHitCoordinate G hG j p (t p)).mp hp
      exact ⟨iff_of_false h.1 ha,iff_of_false h.2 hb⟩

theorem giantCandidateModelOneEachPairs_disjoint {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) :
    Set.PairwiseDisjoint (↑(giantCandidateModelOneEachPairs G) :
      Set (giantCandidateSelectionPrimes G × giantCandidateSelectionPrimes G))
      (fun p => giantCandidateModelOneEachEvent G hG j p.1 p.2) := by
  intro p hp q hq hpq
  apply disjoint_left.mpr
  intro t ht ht'
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have ha := (giantCandidateModelOneEach_residue_iff G hG hq' ht' p.1).1.mp
    ((giantCandidateModelOneEach_residue_iff G hG hp' ht p.1).1.mpr rfl)
  have hb := (giantCandidateModelOneEach_residue_iff G hG hq' ht' p.2).2.mp
    ((giantCandidateModelOneEach_residue_iff G hG hp' ht p.2).2.mpr rfl)
  exact hpq (Prod.ext ha hb)

end
end ArtinMatthews
