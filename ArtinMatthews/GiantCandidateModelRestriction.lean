module

public import ArtinMatthews.GiantCandidateModelMomentRealization


set_option backward.privateInPublic true
@[expose] public section

/-! Restrict a full residue model to the actual primes of a subfamily.
Each group's literal hit set is unchanged under this restriction. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateModelRestrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ)
    (h : giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G) {j : ℕ}
    (t : GiantCandidateModelResidueSpace G j) : GiantCandidateModelResidueSpace D j :=
  fun p => t ⟨p.val,h p.property⟩

theorem giantCandidateModelResidueTuples_mem {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ)
    (t : GiantCandidateModelResidueSpace G j) :
    t∈giantCandidateModelResidueTuples G hG j :=
  Fintype.mem_piFinset.mpr (fun p => giantCandidateModelPrimeCoordinate_mem G hG j p (t p))

theorem giantCandidateModelHitSet_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ)
    (h : giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G)
    (side : ι → GiantCandidateHitSide) (side' : κ → GiantCandidateHitSide)
    (i : ι) (l : κ) (hgroup : G i = D l) (hside : side i=side' l)
    {j : ℕ} (t : GiantCandidateModelResidueSpace G j) :
    giantCandidateModelHitSet G side t i =
      giantCandidateModelHitSet D side' (giantCandidateModelRestrict G D h t) l := by
  ext p
  by_cases hp : p∈G i
  · have hp' : p∈D l := hgroup ▸ hp
    let p₁ : giantCandidateSelectionPrimes G := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨i,hp⟩⟩
    let p₂ : giantCandidateSelectionPrimes D := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨l,hp'⟩⟩
    change p₁.val∈giantCandidateModelHitSet G side t i ↔
      p₂.val∈giantCandidateModelHitSet D side' (giantCandidateModelRestrict G D h t) l
    rw [mem_giantCandidateModelHitSet,mem_giantCandidateModelHitSet]
    have he : giantCandidateModelRestrict G D h t p₂ = t p₁ := rfl
    rw [he,hside]
    exact and_congr_left (fun _ => by change p∈G i ↔ p∈D l; rw [hgroup])
  · have hp' : p∉D l := by simpa only [hgroup] using hp
    exact iff_of_false
      (fun hm => hp (giantCandidateModelHitSet_subset G side t i hm))
      (fun hm => hp' (giantCandidateModelHitSet_subset D side' (giantCandidateModelRestrict G D h t) l hm))

theorem giantCandidateModelHitCounts_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ)
    (h : giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G)
    (side : ι → GiantCandidateHitSide) (side' : κ → GiantCandidateHitSide)
    (i : ι) (l : κ) (hgroup : G i = D l) (hside : side i=side' l)
    {j : ℕ} (t : GiantCandidateModelResidueSpace G j) :
    giantCandidateModelHitCounts G side t i =
      giantCandidateModelHitCounts D side' (giantCandidateModelRestrict G D h t) l :=
  congrArg Finset.card (giantCandidateModelHitSet_restrict G D h side side' i l hgroup hside t)

end
end ArtinMatthews
