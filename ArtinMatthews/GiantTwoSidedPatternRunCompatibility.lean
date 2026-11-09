module

public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.GiantTwoSidedPatternKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual auxiliary ban and signed shift force every common active
prime to be copied. Every genuinely free active prime is coprime to
the complete dilation. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantTwoSidedPatternCopiedValues_card (P : Finset ℕ) {k ell : ℕ}
    (C : Finset (Fin k)) (a : Fin (k+ell) → ↥P) (ha : Function.Injective a) :
    (giantTwoSidedPatternCopiedValues P C a).card = k-C.card := by
  have h : Function.Injective (fun i : Fin k => (a (Fin.castAdd ell i):ℕ)) :=
    Subtype.val_injective.comp (ha.comp (Fin.castAdd_injective k ell))
  rw [giantTwoSidedPatternCopiedValues,card_image_of_injective _ h,card_sdiff_of_subset (subset_univ _),
    card_univ,Fintype.card_fin]

theorem giantTwoSidedPatternCopiedValues_eq {J : Type*}
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)} {s t : MarkedPhysicalMarking P (k+ell)}
    (h : ∀ j (i : Fin k),i∉C j → t j (Fin.castAdd ell i)=s j (Fin.castAdd ell i)) (j : J) :
    giantTwoSidedPatternCopiedValues (P j) (C j) (t j) =
      giantTwoSidedPatternCopiedValues (P j) (C j) (s j) := by
  unfold giantTwoSidedPatternCopiedValues
  exact image_congr (fun i hi => congrArg (fun p : ↥(P j) => p.val) (h j i (mem_sdiff.mp hi).2))

theorem giantTwoSidedPatternCopiedProduct_dvd_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell : ℕ}
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) (j : J) {p : ℕ} (hp : p∈P j) :
    p ∣ giantTwoSidedPatternCopiedProduct C a ↔
      p∈giantTwoSidedPatternCopiedValues (P j) (C j) (a j) := by
  have hprime := hP j p hp
  simp only [giantTwoSidedPatternCopiedProduct,giantTwoSidedPatternCopiedValues,
    hprime.prime.dvd_finsetProd_iff,mem_univ,true_and,mem_image]
  constructor
  · rintro ⟨l,i,hi,hd⟩
    have he := ((hP l _ (a l (Fin.castAdd ell i)).property).dvd_iff_eq hprime.ne_one).mp hd
    have hl : p∈P l := he ▸ (a l (Fin.castAdd ell i)).property
    have hj : l=j := by
      by_contra hne
      exact disjoint_left.mp (hdis hne) hl hp
    subst l
    exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨j,i,hi,dvd_rfl⟩

theorem giantTwoSidedPatternAuxiliaryProduct_dvd_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {k : ℕ} {C : J → Finset (Fin k)}
    (a : GiantTwoSidedPatternAuxiliary P C) {p : ℕ} (hp : p.Prime) :
    p ∣ giantTwoSidedPatternAuxiliaryProduct a ↔ ∃ (j : J) (i : ↥(C j)),(a j i:ℕ)=p := by
  simp only [giantTwoSidedPatternAuxiliaryProduct,hp.prime.dvd_finsetProd_iff,mem_univ,true_and]
  constructor
  · rintro ⟨j,i,hd⟩
    exact ⟨j,i,((hP j _ (a j i).property).dvd_iff_eq hp.ne_one).mp hd⟩
  · rintro ⟨j,i,rfl⟩
    exact ⟨j,i,dvd_rfl⟩

theorem giantTwoSidedPattern_dilation_dvd_iff_of_active {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell : ℕ} {C : J → Finset (Fin k)}
    {step : ℤ} {Z Z' : Finset ℕ} {s : GiantTwoSidedEndpointState P (k+ell) Z}
    {t : GiantTwoSidedEndpointState P (k+ell) Z'} {a : GiantTwoSidedPatternAuxiliary P C}
    (h : GiantTwoSidedPatternCondition C step s t a) (j : J) {p : ℕ}
    (hp : p∈markedPhysicalLabelSet s.val.2 j ∨ p∈markedPhysicalLabelSet t.val.2 j) :
    p ∣ giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a ↔
      p∈giantTwoSidedPatternCopiedValues (P j) (C j) (s.val.2 j) := by
  have hpP : p∈P j := hp.elim (fun h => markedPhysicalLabelSet_subset _ _ h)
    (fun h => markedPhysicalLabelSet_subset _ _ h)
  have hprime := hP j p hpP
  have haux : ¬p ∣ giantTwoSidedPatternAuxiliaryProduct a := by
    intro hdiv
    obtain ⟨g,i,he⟩ := (giantTwoSidedPatternAuxiliaryProduct_dvd_iff hP a hprime).mp hdiv
    rcases hp with hs | ht
    · obtain ⟨l,_,hl⟩ := mem_image.mp hs
      exact (h.2.2 g j i l).1 (he.trans hl.symm)
    · obtain ⟨l,_,hl⟩ := mem_image.mp ht
      exact (h.2.2 g j i l).2 (he.trans hl.symm)
  rw [hprime.dvd_mul,or_iff_left haux]
  exact giantTwoSidedPatternCopiedProduct_dvd_iff hP hdis C s.val.2 j hpP

theorem giantTwoSidedPattern_common_labels {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell : ℕ} {C : J → Finset (Fin k)}
    {step : ℤ} (hstep : 0<step.natAbs) (hsize : ∀ j p,p∈P j → step.natAbs<p)
    {Z Z' : Finset ℕ} {s : GiantTwoSidedEndpointState P (k+ell) Z}
    {t : GiantTwoSidedEndpointState P (k+ell) Z'} {a : GiantTwoSidedPatternAuxiliary P C}
    (h : GiantTwoSidedPatternCondition C step s t a) (j : J) :
    markedPhysicalLabelSet s.val.2 j ∩ markedPhysicalLabelSet t.val.2 j =
      giantTwoSidedPatternCopiedValues (P j) (C j) (s.val.2 j) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hs,ht⟩ := mem_inter.mp hp
    have hmem := markedPhysicalLabelSet_subset s.val.2 j hs
    have hprime := hP j p hmem
    let D := giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a
    have hsd : p∣s.val.1.val := by
      obtain ⟨l,_,hl⟩ := mem_image.mp hs
      exact hl ▸ s.property.2 j l
    have htd : p∣t.val.1.val := by
      obtain ⟨l,_,hl⟩ := mem_image.mp ht
      exact hl ▸ t.property.2 j l
    have hshift : (t.val.1.val:ℤ)=(s.val.1.val:ℤ)+step*(D:ℤ) := h.2.1
    have hd := dvd_sub (Int.natCast_dvd_natCast.mpr htd) (Int.natCast_dvd_natCast.mpr hsd)
    rw [hshift,add_sub_cancel_left] at hd
    have hn : p∣step.natAbs*D := by
      simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
    have hnd : ¬p∣step.natAbs := fun hdiv => (not_le_of_gt (hsize j p hmem)) (Nat.le_of_dvd hstep hdiv)
    exact (giantTwoSidedPattern_dilation_dvd_iff_of_active hP hdis h j (Or.inl hs)).mp
      ((hprime.dvd_mul.mp hn).resolve_left hnd)
  · intro hp
    obtain ⟨i,hi,he⟩ := mem_image.mp hp
    have hcopy := h.1 j i (mem_sdiff.mp hi).2
    exact mem_inter.mpr ⟨mem_image.mpr ⟨Fin.castAdd ell i,mem_univ _,he⟩,
      mem_image.mpr ⟨Fin.castAdd ell i,mem_univ _,(congrArg (fun a : ↥(P j) => a.val) hcopy).trans he⟩⟩

end
end ArtinMatthews
