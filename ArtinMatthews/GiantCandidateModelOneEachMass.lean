module

public import ArtinMatthews.GiantCandidateModelOneEachEvent


set_option backward.privateInPublic true
@[expose] public section

/-! The exact probability for a specified pair of unique hits has
both hit atoms and every other prime's no-hit atom. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateModelOneEach_mass_eq {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (a b : giantCandidateSelectionPrimes G) (hab : a≠b) :
    ((giantCandidateModelOneEachEvent G hG j a b).card:ℝ)/
      ((giantCandidateModelResidueTuples G hG j).card:ℝ) =
      giantCandidateModelHitAtom G hG j a .predecessor*giantCandidateModelHitAtom G hG j b .product*
        ∏ p∈((univ : Finset (giantCandidateSelectionPrimes G)).erase a).erase b,
          giantCandidateModelNoHitAtom G hG j p := by
  let U := giantCandidateSelectionPrimes G
  let S := (univ : Finset U).erase a
  let T := S.erase b
  let f (p : U) := ((giantCandidateModelOneEachCoordinate G hG j a b p).card:ℝ)/(p.val:ℝ)^j
  let w (p : U) := giantCandidateModelNoHitAtom G hG j p
  have ha : f a=giantCandidateModelHitAtom G hG j a .predecessor := by
    dsimp only [f]
    rw [giantCandidateModelOneEachCoordinate,ite_eq_left rfl,giantCandidateModelHitAtom]
  have hb : f b=giantCandidateModelHitAtom G hG j b .product := by
    dsimp only [f]
    rw [giantCandidateModelOneEachCoordinate,ite_eq_right hab.symm,ite_eq_left rfl,giantCandidateModelHitAtom]
  have hbS : b∈S := mem_erase.mpr ⟨hab.symm,mem_univ _⟩
  have hrest : (∏ p∈T,f p)=∏ p∈T,w p := by
    apply prod_congr rfl
    intro p hp
    have hpa := (mem_erase.mp (mem_erase.mp hp).2).1
    have hpb := (mem_erase.mp hp).1
    dsimp only [f,w]
    rw [giantCandidateModelOneEachCoordinate,ite_eq_right hpa,ite_eq_right hpb,giantCandidateModelNoHitAtom]
  rw [giantCandidateModelOneEachEvent,Fintype.card_piFinset,giantCandidateModelResidueTuples_card]
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [← prod_div_distrib]
  change (∏ p : U,f p) = giantCandidateModelHitAtom G hG j a .predecessor*
    giantCandidateModelHitAtom G hG j b .product*∏ p∈T,w p
  rw [← mul_prod_erase univ f (mem_univ a),← mul_prod_erase S f hbS,ha,hb,hrest,mul_assoc]

theorem giantCandidateModelOneEach_mass_ge_full_noHit {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (a b : giantCandidateSelectionPrimes G) (hab : a≠b) :
    giantCandidateModelHitAtom G hG j a .predecessor*giantCandidateModelHitAtom G hG j b .product*
      (∏ p : giantCandidateSelectionPrimes G,giantCandidateModelNoHitAtom G hG j p) ≤
    ((giantCandidateModelOneEachEvent G hG j a b).card:ℝ)/
      ((giantCandidateModelResidueTuples G hG j).card:ℝ) := by
  rw [giantCandidateModelOneEach_mass_eq G hG j a b hab]
  apply mul_le_mul_of_nonneg_left _ (by unfold giantCandidateModelHitAtom; positivity)
  exact prod_le_prod_of_subset_of_le_one₀ (subset_univ _)
    (fun p _ => (giantCandidateModelNoHitAtom_mem_unitInterval G hG j p).1)
    (fun p _ _ => (giantCandidateModelNoHitAtom_mem_unitInterval G hG j p).2)

end
end ArtinMatthews
