module

public import ArtinMatthews.GiantCandidateModelRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The independent residue carrier on a disjoint union is the product
of the two literal restricted carriers. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateModelSubfamily_left {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    {G : ι → Finset ℕ} {D : κ → Finset ℕ} {E : ζ → Finset ℕ}
    (h : giantCandidateSelectionPrimes G =
      giantCandidateSelectionPrimes D ∪ giantCandidateSelectionPrimes E) :
    giantCandidateSelectionPrimes D ⊆ giantCandidateSelectionPrimes G := by
  rw [h]
  exact subset_union_left

theorem giantCandidateModelSubfamily_right {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    {G : ι → Finset ℕ} {D : κ → Finset ℕ} {E : ζ → Finset ℕ}
    (h : giantCandidateSelectionPrimes G =
      giantCandidateSelectionPrimes D ∪ giantCandidateSelectionPrimes E) :
    giantCandidateSelectionPrimes E ⊆ giantCandidateSelectionPrimes G := by
  rw [h]
  exact subset_union_right

def giantCandidateModelResidueSplit {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ) (E : ζ → Finset ℕ)
    (h : giantCandidateSelectionPrimes G =
      giantCandidateSelectionPrimes D ∪ giantCandidateSelectionPrimes E)
    (hd : Disjoint (giantCandidateSelectionPrimes D) (giantCandidateSelectionPrimes E)) (j : ℕ) :
    GiantCandidateModelResidueSpace G j ≃
      GiantCandidateModelResidueSpace D j × GiantCandidateModelResidueSpace E j where
  toFun t := ⟨giantCandidateModelRestrict G D (giantCandidateModelSubfamily_left h) t,
    giantCandidateModelRestrict G E (giantCandidateModelSubfamily_right h) t⟩
  invFun t p :=
    if hp : p.val∈giantCandidateSelectionPrimes D then t.1 ⟨p.val,hp⟩
    else t.2 ⟨p.val,(mem_union.mp (h ▸ p.property)).resolve_left hp⟩
  left_inv t := by
    funext p
    dsimp only [giantCandidateModelRestrict]
    split_ifs <;> rfl
  right_inv t := by
    apply Prod.ext
    · funext p
      dsimp only [giantCandidateModelRestrict]
      rw [dite_eq_left p.property]
    · funext p
      dsimp only [giantCandidateModelRestrict]
      have hp : p.val∉giantCandidateSelectionPrimes D := fun h' => disjoint_left.mp hd h' p.property
      rw [dite_eq_right hp]

theorem giantCandidateModelResidueMean_mul_eq {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    (G : ι → Finset ℕ) (D : κ → Finset ℕ) (E : ζ → Finset ℕ)
    (h : giantCandidateSelectionPrimes G =
      giantCandidateSelectionPrimes D ∪ giantCandidateSelectionPrimes E)
    (hd : Disjoint (giantCandidateSelectionPrimes D) (giantCandidateSelectionPrimes E))
    (hG : ∀ i p,p∈G i → p.Prime) (hD : ∀ i p,p∈D i → p.Prime) (hE : ∀ i p,p∈E i → p.Prime)
    (j : ℕ) (f : GiantCandidateModelResidueSpace D j → ℝ) (g : GiantCandidateModelResidueSpace E j → ℝ) :
    (𝔼 t∈giantCandidateModelResidueTuples G hG j,
      f (giantCandidateModelRestrict G D (giantCandidateModelSubfamily_left h) t)*
        g (giantCandidateModelRestrict G E (giantCandidateModelSubfamily_right h) t)) =
      (𝔼 t∈giantCandidateModelResidueTuples D hD j,f t)*
      (𝔼 t∈giantCandidateModelResidueTuples E hE j,g t) := by
  let S := giantCandidateModelResidueTuples D hD j
  let T := giantCandidateModelResidueTuples E hE j
  let e := giantCandidateModelResidueSplit G D E h hd j
  calc
    _ = 𝔼 t∈S×ˢT,f t.1*g t.2 := by
      apply expect_equiv e
      · intro t
        exact iff_of_true (giantCandidateModelResidueTuples_mem G hG j t)
          (mem_product.mpr ⟨giantCandidateModelResidueTuples_mem D hD j (e t).1,
            giantCandidateModelResidueTuples_mem E hE j (e t).2⟩)
      · exact fun _ _ => rfl
    _ = _ := by rw [expect_product,← expect_mul_expect]

end
end ArtinMatthews
