module

public import ArtinMatthews.GiantComparisonSharedCollision
public import ArtinMatthews.GiantTwoSidedSharedCollision


set_option backward.privateInPublic true
@[expose] public section

/-! Each copied complement has its own harmonic product law. The union
bound uses its actual number of slots and the original band mass. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {P : J → Finset ℕ} {k : ℕ} {C : J → Finset (Fin k)}

def giantComparisonSharedForbidden (aux : GiantTwoSidedPatternAuxiliary P C)
    (w w' : ℕ) (j : J) : Finset ↥(P j) :=
  giantTwoSidedSharedForbidden (P j) (w*w') ∪ univ.image (aux j)

theorem giantComparisonSharedForbidden_mem (hP : ∀ j p, p ∈ P j → p.Prime)
    (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ) (j : J) (p : ↥(P j)) :
    p ∈ giantComparisonSharedForbidden aux w w' j ↔
      (p : ℕ) ∣ w ∨ (p : ℕ) ∣ w' ∨ ∃ i : ↥(C j), aux j i = p := by
  simp only [giantComparisonSharedForbidden, giantTwoSidedSharedForbidden, mem_union,
    mem_filter, mem_univ, true_and, mem_image, (hP j p.val p.property).dvd_mul, or_assoc]

theorem giantComparisonSharedGood_complement (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ) (c : GiantComparisonSharedLabels P C) :
    ¬ GiantComparisonSharedGood aux w w' c ↔
      ∃ j, MarkedPadCollision (giantComparisonSharedForbidden aux w w' j) (c j) := by
  constructor
  · intro h
    by_contra hn
    apply h
    refine ⟨?_, ?_, ?_⟩
    · intro j i l he
      by_contra hne
      exact hn ⟨j, Or.inl ⟨i, l, hne, he⟩⟩
    · intro j i
      have hf := giantComparisonSharedForbidden_mem hP aux w w' j (c j i)
      exact ⟨fun hd => hn ⟨j, Or.inr ⟨i, hf.mpr (Or.inl hd)⟩⟩,
        fun hd => hn ⟨j, Or.inr ⟨i, hf.mpr (Or.inr (Or.inl hd))⟩⟩⟩
    · intro g j i l he
      have hgj : g = j := by
        by_contra hne
        exact disjoint_left.mp (hdis hne) (he ▸ (aux g i).property) (c j l).property
      subst g
      have hf := giantComparisonSharedForbidden_mem hP aux w w' j (c j l)
      exact hn ⟨j, Or.inr ⟨l, hf.mpr (Or.inr (Or.inr ⟨i, Subtype.ext he⟩))⟩⟩
  · rintro ⟨j, h⟩ hg
    rcases h with ⟨i, l, hne, he⟩ | ⟨i, hi⟩
    · exact hne (hg.1 j he)
    · rcases (giantComparisonSharedForbidden_mem hP aux w w' j (c j i)).mp hi with
        hd | hd | ⟨l, hl⟩
      · exact (hg.2.1 j i).1 hd
      · exact (hg.2.1 j i).2 hd
      · exact hg.2.2 j j l i (congrArg Subtype.val hl)

theorem giantComparisonSharedForbidden_card_le (hP : ∀ j p, p ∈ P j → p.Prime)
    (aux : GiantTwoSidedPatternAuxiliary P C) {w w' : ℕ} (hw : 0 < w) (hw' : 0 < w') (j : J) :
    ((giantComparisonSharedForbidden aux w w' j).card : ℝ) ≤
      Real.log ((w*w' : ℕ) : ℝ) / Real.log (3/2) + (C j).card := by
  unfold giantComparisonSharedForbidden
  have haux : (univ.image (aux j)).card ≤ (C j).card := by
    simpa only [card_univ, Fintype.card_coe] using
      (card_image_le (s := (univ : Finset ↥(C j))) (f := aux j))
  calc
    _ ≤ ((giantTwoSidedSharedForbidden (P j) (w*w')).card : ℝ) + (univ.image (aux j)).card := by
      exact_mod_cast card_union_le (giantTwoSidedSharedForbidden (P j) (w*w')) (univ.image (aux j))
    _ ≤ _ := add_le_add
      (giantTwoSidedSharedForbidden_card_le (P j) (hP j) (Nat.mul_pos hw hw'))
      (Nat.cast_le.mpr haux)

variable [Fintype J] [DecidableEq J]

theorem giantComparisonSharedCollision_group_mass (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (A : (j : J) → Finset ↥(P j)) (j : J) :
    markedEventMass (giantComparisonSharedMass (C := C))
        (fun c => MarkedPadCollision (A j) (c j)) =
      markedEventMass (finiteProductMass (fun _ : ↥(univ \ C j) => markedHarmonicAtom (P j)))
        (MarkedPadCollision (A j)) := by
  let μ (j : J) (c : ↥(univ \ C j) → ↥(P j)) := ∏ i, markedHarmonicAtom (P j) (c i)
  let f (j : J) (c : ↥(univ \ C j) → ↥(P j)) := if MarkedPadCollision (A j) c then (1 : ℝ) else 0
  have hμ (j : J) : (∑ c : ↥(univ \ C j) → ↥(P j), μ j c) = 1 := by
    dsimp only [μ]
    rw [← Fintype.prod_sum (fun (_ : ↥(univ \ C j)) (p : ↥(P j)) => markedHarmonicAtom (P j) p)]
    simp only [markedHarmonicAtom_sum (P j) (hV j), prod_const_one]
  simpa only [markedEventMass, giantComparisonSharedMass, giantTwoSidedPatternAuxiliaryMass,
    finiteProductMass, μ, f] using finiteProduct_expectation_coordinate μ f hμ j

theorem giantComparisonSharedBadMass_le (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (aux : GiantTwoSidedPatternAuxiliary P C) {w w' : ℕ} (hw : 0 < w) (hw' : 0 < w')
    {y : ℝ} (hy : 0 < y) (hlarge : ∀ j p, p ∈ P j → y ≤ (p : ℝ)) :
    giantComparisonSharedBadMass aux w w' ≤
      ∑ j, (((univ \ C j).card : ℝ)^2 + ((univ \ C j).card : ℝ)*
        (Real.log ((w*w' : ℕ) : ℝ) / Real.log (3/2) + (C j).card)) *
        (1 / (y*bandReciprocalMass (P j))) := by
  let A := giantComparisonSharedForbidden aux w w'
  have hμ (c : GiantComparisonSharedLabels P C) : 0 ≤ giantComparisonSharedMass c :=
    giantTwoSidedPatternAuxiliaryMass_nonneg hV c
  rw [giantComparisonSharedBadMass_eq_event]
  simp_rw [giantComparisonSharedGood_complement hP hdis aux w w']
  apply (markedEventMass_exists_le giantComparisonSharedMass hμ
    (fun j c => MarkedPadCollision (A j) (c j))).trans
  apply sum_le_sum
  intro j _
  rw [giantComparisonSharedCollision_group_mass hV A j]
  have hj := marked_iid_pad_collision_bound (I := ↥(univ \ C j))
    (markedHarmonicAtom (P j)) (fun _ => markedHarmonicAtom_nonneg (P j) (hV j))
    (markedHarmonicAtom_sum (P j) (hV j)) (A j) (markedHarmonicAtom_le (P j) (hV j) hy (hlarge j))
  simp only [Fintype.card_coe] at hj
  apply hj.trans
  apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr (mul_nonneg hy.le (hV j).le))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (giantComparisonSharedForbidden_card_le hP aux hw hw' j) (Nat.cast_nonneg _))

end
end ArtinMatthews
