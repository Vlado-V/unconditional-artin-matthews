module

public import ArtinMatthews.GiantCandidateSelectionPrimeMask
public import ArtinMatthews.GiantCandidatePrimeHitProbabilities


set_option backward.privateInPublic true
@[expose] public section

/-! Repeating a selected prime on opposite sides gives an empty event.
With same-side group disjointness, each surviving branch is bounded by
the product of the reciprocal-prime atom bounds. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateSelectionPrimeMask_eq_empty_of_conflict {ι : Type*} [Fintype ι]
    (D : ι → Finset ℕ) (side : ι → GiantCandidateHitSide)
    (hP : ∀ p∈giantCandidateSelectionPrimes D,p.Prime)
    (j : ℕ) (p : giantCandidateSelectionPrimes D) {i l : ι}
    (hi : p.val∈D i) (hl : p.val∈D l) (hs : side i≠side l) :
    giantCandidateSelectionPrimeMask D side hP j p = ∅ := by
  let _ : Fact p.val.Prime := ⟨hP p.val p.property⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h₁ := (mem_giantCandidateSelectionPrimeMask D side hP p t).mp ht i hi
  have h₂ := (mem_giantCandidateSelectionPrimeMask D side hP p t).mp ht l hl
  cases hsi : side i <;> cases hsl : side l
  · exact hs (hsi.trans hsl.symm)
  · rw [hsi] at h₁
    rw [hsl] at h₂
    exact one_ne_zero (h₁.symm.trans h₂)
  · rw [hsi] at h₁
    rw [hsl] at h₂
    exact one_ne_zero (h₂.symm.trans h₁)
  · exact hs (hsi.trans hsl.symm)

private theorem giantCandidateSelectionPrimeMask_atom_le {ι : Type*} [Fintype ι]
    (D : ι → Finset ℕ) (side : ι → GiantCandidateHitSide)
    (hP : ∀ p∈giantCandidateSelectionPrimes D,p.Prime)
    {j : ℕ} (hj : 0<j) (p : giantCandidateSelectionPrimes D) :
    ((giantCandidateSelectionPrimeMask D side hP j p).card:ℝ)/(p.val:ℝ)^j ≤
      (j:ℝ)/(p.val:ℝ) := by
  let _ : Fact p.val.Prime := ⟨hP p.val p.property⟩
  obtain ⟨i,hi⟩ := mem_giantCandidateSelectionPrimes.mp p.property
  have hsub : giantCandidateSelectionPrimeMask D side hP j p ⊆
      giantCandidatePrimeHitMask p.val j (side i) := by
    intro t ht
    exact (mem_giantCandidatePrimeHitMask (side i) t).mpr
      ((mem_giantCandidateSelectionPrimeMask D side hP p t).mp ht i hi)
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (by positivity)).trans
    (giantCandidatePrimeHitProbability_le p.val j hj (side i))

theorem giantCandidateSelectionModelMass_le_product {ι : Type*} [Fintype ι]
    {G : ι → Finset ℕ} {k : ι → ℕ} {D : ι → Finset ℕ}
    (hD : D∈giantCandidateHitSelections G k)
    (side : ι → GiantCandidateHitSide)
    (hdis : Pairwise (fun i l => side i=side l → Disjoint (G i) (G l)))
    (hP : ∀ p∈giantCandidateSelectionPrimes D,p.Prime) {j : ℕ} (hj : 0<j) :
    (∏ p : giantCandidateSelectionPrimes D,
      ((giantCandidateSelectionPrimeMask D side hP j p).card:ℝ)/(p.val:ℝ)^j) ≤
        ∏ i,∏ p∈D i,(j:ℝ)/(p:ℝ) := by
  classical
  let U := giantCandidateSelectionPrimes D
  let w (p : ℕ) : ℝ := (j:ℝ)/(p:ℝ)
  let A (p : U) := ((giantCandidateSelectionPrimeMask D side hP j p).card:ℝ)/(p.val:ℝ)^j
  have hw (p : ℕ) : 0≤w p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hAtom (p : U) : A p ≤ w p.val := giantCandidateSelectionPrimeMask_atom_le D side hP hj p
  by_cases hd : Pairwise (fun i l => Disjoint (D i) (D l))
  · have hprod : (∏ p : U,w p.val) = ∏ i,∏ p∈D i,w p := by
      rw [prod_coe_sort]
      change (∏ p∈univ.biUnion D,w p) = _
      exact prod_biUnion (fun i _ l _ hi => hd hi)
    change (∏ p : U,A p) ≤ ∏ i,∏ p∈D i,w p
    rw [← hprod]
    exact prod_le_prod₀ (fun p _ => by dsimp only [A]; positivity) (fun p _ => hAtom p)
  · have he : ∃ i l,i≠l ∧ ¬Disjoint (D i) (D l) := by
      by_contra hn
      apply hd
      intro i l hil
      by_contra h
      exact hn ⟨i,l,hil,h⟩
    obtain ⟨i,l,hil,hn⟩ := he
    obtain ⟨p,hpi,hpl⟩ := not_disjoint_iff.mp hn
    let q : U := ⟨p,mem_giantCandidateSelectionPrimes.mpr ⟨i,hpi⟩⟩
    have hs : side i≠side l := by
      intro hs
      exact (disjoint_left.mp (hdis hil hs)) ((mem_giantCandidateHitSelections.mp hD i).1 hpi)
        ((mem_giantCandidateHitSelections.mp hD l).1 hpl)
    have hzero : A q=0 := by
      dsimp only [A]
      rw [giantCandidateSelectionPrimeMask_eq_empty_of_conflict D side hP j q hpi hpl hs,
        card_empty,Nat.cast_zero,zero_div]
    change (∏ p : U,A p) ≤ ∏ i,∏ p∈D i,w p
    rw [prod_eq_zero (mem_univ q) hzero]
    exact prod_nonneg (fun i _ => prod_nonneg (fun p _ => hw p))

end
end ArtinMatthews
