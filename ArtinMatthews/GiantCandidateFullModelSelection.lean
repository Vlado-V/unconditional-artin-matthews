module

public import ArtinMatthews.GiantCandidateFullResidueModel


set_option backward.privateInPublic true
@[expose] public section

/-! Selected-prime model events restrict exactly the indicated
coordinates of the full independent residue carrier. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateModelSelectionCoordinate {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (D : giantCandidateHitSelections G k)
    (p : giantCandidateSelectionPrimes G) : Finset (Fin j → ZMod p.val) :=
  if hp : p.val∈giantCandidateSelectionPrimes D.val then
    giantCandidateSelectionPrimeMask D.val side (giantCandidateSelectionPrimes_prime D.property hG) j ⟨p.val,hp⟩
  else giantCandidateModelPrimeCoordinate G hG j p

theorem giantCandidateModelSelection_filter_eq {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (D : giantCandidateHitSelections G k) :
    (giantCandidateModelResidueTuples G hG j).filter
      (fun t => ∀ i,D.val i⊆giantCandidateModelHitSet G side t i) =
      Fintype.piFinset (giantCandidateModelSelectionCoordinate G side k hG j D) := by
  classical
  let U := giantCandidateSelectionPrimes G
  let V := giantCandidateSelectionPrimes D.val
  let hP := giantCandidateSelectionPrimes_prime D.property hG
  ext t
  constructor
  · intro ht
    apply Fintype.mem_piFinset.mpr
    intro p
    unfold giantCandidateModelSelectionCoordinate
    by_cases hp : p.val∈V
    · rw [dite_eq_left hp]
      apply (mem_giantCandidateSelectionPrimeMask D.val side hP ⟨p.val,hp⟩ _).mpr
      intro i hi
      exact ((mem_giantCandidateModelHitSet G side t i p).mp ((mem_filter.mp ht).2 i hi)).2
    · rw [dite_eq_right hp]
      exact giantCandidateModelPrimeCoordinate_mem G hG j p _
  · intro ht
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun p => giantCandidateModelPrimeCoordinate_mem G hG j p _),?_⟩
    intro i p hp
    have hpG := (mem_giantCandidateHitSelections.mp D.property i).1 hp
    let p₀ : U := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨i,hpG⟩⟩
    have hpD : p₀.val∈V := mem_giantCandidateSelectionPrimes.mpr ⟨i,hp⟩
    have hh := Fintype.mem_piFinset.mp ht p₀
    rw [giantCandidateModelSelectionCoordinate,dite_eq_left hpD] at hh
    have hr := (mem_giantCandidateSelectionPrimeMask D.val side hP ⟨p₀.val,hpD⟩ _).mp hh i hp
    exact (mem_giantCandidateModelHitSet G side t i p₀).mpr ⟨hpG,hr⟩

theorem giantCandidateModelSelection_mass {ι : Type*} [Fintype ι]
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (D : giantCandidateHitSelections G k) :
    (((giantCandidateModelResidueTuples G hG j).filter
      (fun t => ∀ i,D.val i⊆giantCandidateModelHitSet G side t i)).card:ℝ)/
      ((giantCandidateModelResidueTuples G hG j).card:ℝ) =
      ∏ p : giantCandidateSelectionPrimes D.val,
        ((giantCandidateSelectionPrimeMask D.val side
          (giantCandidateSelectionPrimes_prime D.property hG) j p).card:ℝ)/(p.val:ℝ)^j := by
  classical
  let U := giantCandidateSelectionPrimes G
  let V := giantCandidateSelectionPrimes D.val
  let hP := giantCandidateSelectionPrimes_prime D.property hG
  let A := (univ : Finset U).filter (fun p => p.val∈V)
  let f (p : U) := ((giantCandidateModelSelectionCoordinate G side k hG j D p).card:ℝ)/(p.val:ℝ)^j
  let g (p : V) := ((giantCandidateSelectionPrimeMask D.val side hP j p).card:ℝ)/(p.val:ℝ)^j
  have hsub : V ⊆ U := giantCandidateSelectionPrimes_subset D.property (fun i _ hp =>
    mem_giantCandidateSelectionPrimes.mpr ⟨i,hp⟩)
  rw [giantCandidateModelSelection_filter_eq G side k hG j D,Fintype.card_piFinset,
    giantCandidateModelResidueTuples_card]
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [← prod_div_distrib]
  change (∏ p : U,f p) = ∏ p : V,g p
  calc
    _ = ∏ p∈A,f p := by
      symm
      apply prod_subset (filter_subset _ _)
      intro p _ hp
      have hnot : p.val∉V := fun h => hp (mem_filter.mpr ⟨mem_univ _,h⟩)
      obtain ⟨i,hi⟩ := mem_giantCandidateSelectionPrimes.mp p.property
      dsimp only [f]
      rw [giantCandidateModelSelectionCoordinate,dite_eq_right hnot,
        giantCandidateModelPrimeCoordinate_card,Nat.cast_pow,
        div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr (hG i p.val hi).ne_zero))]
    _ = _ := by
      apply prod_bij (fun p hp => (⟨p.val,(mem_filter.mp hp).2⟩ : V))
      · exact fun _ _ => mem_univ _
      · intro p hp q hq he
        exact Subtype.ext (congrArg (fun a : V => a.val) he)
      · intro p _
        exact ⟨⟨p.val,hsub p.property⟩,mem_filter.mpr ⟨mem_univ _,p.property⟩,Subtype.ext rfl⟩
      · intro p hp
        have h : p.val∈V := (mem_filter.mp hp).2
        dsimp only [f,g]
        rw [giantCandidateModelSelectionCoordinate,dite_eq_left h]

end
end ArtinMatthews
