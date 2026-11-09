module

public import ArtinMatthews.MarkedPhysicalRootLineMass
public import ArtinMatthews.MarkedPhysicalOneEdgeMass


set_option backward.privateInPublic true
@[expose] public section

/-! The finite root-line density is the original one-edge union-label
charge, with no repeated prime and no lost ordered-list multiplicity. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRootLineMass_eq_projectiveProduct
    {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) :
    markedPhysicalRootLineMass (markedPhysicalMarkingProduct a) =
      markedPhysicalProjectiveProduct a := by
  classical
  let S := markedPhysicalMarkingProduct a
  have hS : S ≠ 0 := (markedPhysicalMarkingProduct_pos hP a).ne'
  let f : J × Fin M → S.primeFactors := fun i => ⟨(a i.1 i.2 : ℕ),
    Nat.mem_primeFactors.mpr ⟨hP i.1 _ (a i.1 i.2).2,
      (markedPhysicalMarkingProduct_prime_dvd_iff hP a (hP i.1 _ (a i.1 i.2).2)).mpr
        ⟨i.1,i.2,rfl⟩, hS⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact markedPhysicalMarking_global_injective hdis a ha (congrArg Subtype.val hij)
    · intro p
      have hp := Nat.mem_primeFactors.mp p.2
      obtain ⟨j,k,hjk⟩ := (markedPhysicalMarkingProduct_prime_dvd_iff hP a hp.1).mp hp.2.1
      exact ⟨(j,k),Subtype.ext hjk.symm⟩
  let E : (J × Fin M) ≃ S.primeFactors := Equiv.ofBijective f hf
  unfold markedPhysicalRootLineMass markedPhysicalProjectiveProduct
  rw [← Fintype.prod_prod_type (fun i : J × Fin M => 1/((a i.1 i.2 : ℝ)+1))]
  exact (Equiv.prod_comp E (fun p : S.primeFactors => (1/((p : ℕ)+1 : ℝ)))).symm

theorem markedPhysicalRoot_union_forced_line_count_le
    {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    [NeZero (markedPhysicalMarkingProduct a)]
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct a)) → Prop)
    (ℓ : MarkedRootLineTuple (markedPhysicalMarkingProduct a))
    (hE : ∀ g, E g → markedRootKernelTuple (markedPhysicalMarkingProduct_squarefree hP hdis a ha) g = ℓ) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct a)),
      if E g then (1 : ℝ) else 0) /
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct a))) : ℝ) ≤
      markedPhysicalProjectiveProduct a := by
  rw [← markedPhysicalRootLineMass_eq_projectiveProduct hP hdis a ha]
  exact markedPhysicalRoot_forced_line_count_le
    (markedPhysicalMarkingProduct_squarefree hP hdis a ha) E ℓ hE

end ArtinMatthews
