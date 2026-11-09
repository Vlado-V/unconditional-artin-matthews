module

public import ArtinMatthews.KummerRowIndividualDegree
public import ArtinMatthews.ArtinFrobeniusTowerTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! The actual one-parameter Kummer field embeds into its common row
field. Restricting automorphisms carries the same chosen radical root,
and the individual radical character pulls back to the common character. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section

variable {F : Type} [Field F] [Algebra F ℂ]

theorem sixthKummerRowField_mono {A B : Finset F} (hAB : A ⊆ B) :
    sixthKummerRowField A ≤ sixthKummerRowField B := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro z hz
  apply IntermediateField.subset_adjoin
  rcases (mem_sixthKummerRowPolynomial_rootSet A z).mp hz with hz | ⟨a,ha,hz⟩
  · exact (mem_sixthKummerRowPolynomial_rootSet B z).mpr (Or.inl hz)
  · exact (mem_sixthKummerRowPolynomial_rootSet B z).mpr (Or.inr ⟨a,hAB ha,hz⟩)

def sixthKummerIndividualInclusion (A : Finset F) (a : F) (ha : a ∈ A) :
    sixthKummerRowField {a} →ₐ[F] sixthKummerRowField A :=
  IntermediateField.inclusion (sixthKummerRowField_mono (Finset.singleton_subset_iff.mpr ha))

theorem sixthKummerIndividualInclusion_coe (A : Finset F) (a : F) (ha : a ∈ A)
    (x : sixthKummerRowField {a}) : ((sixthKummerIndividualInclusion A a ha x :
      sixthKummerRowField A) : ℂ)=(x:ℂ) := by
  unfold sixthKummerIndividualInclusion
  exact IntermediateField.coe_inclusion _ x

theorem sixthKummerIndividualInclusion_root (A : Finset F) (a : F) (ha : a ∈ A) :
    sixthKummerIndividualInclusion A a ha
      (sixthKummerRowRoot {a} a (Finset.mem_singleton_self a))=sixthKummerRowRoot A a ha := rfl

@[instance_reducible] def sixthKummerIndividualAlgebra (A : Finset F) (a : F) (ha : a ∈ A) :
    Algebra (sixthKummerRowField {a}) (sixthKummerRowField A) :=
  (sixthKummerIndividualInclusion A a ha).toAlgebra

def sixthKummerRowRestriction (A : Finset F) (a : F) (ha : a ∈ A) :
    Gal(sixthKummerRowField A/F) →* Gal(sixthKummerRowField {a}/F) := by
  letI := sixthKummerIndividualAlgebra A a ha
  letI : IsScalarTower F (sixthKummerRowField {a}) (sixthKummerRowField A) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact AlgEquiv.restrictNormalHom (sixthKummerRowField {a})

theorem sixthKummerRowRestriction_commutes (A : Finset F) (a : F) (ha : a ∈ A)
    (σ : Gal(sixthKummerRowField A/F)) (x : sixthKummerRowField {a}) :
    sixthKummerIndividualInclusion A a ha (sixthKummerRowRestriction A a ha σ x)=
      σ (sixthKummerIndividualInclusion A a ha x) := by
  let := sixthKummerIndividualAlgebra A a ha
  let : IsScalarTower F (sixthKummerRowField {a}) (sixthKummerRowField A) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact AlgEquiv.restrictNormal_commutes σ (sixthKummerRowField {a}) x

theorem sixthKummerRowRestriction_root (A : Finset F) (a : F) (ha : a ∈ A)
    (σ : Gal(sixthKummerRowField A/F)) :
    ((sixthKummerRowRestriction A a ha σ
      (sixthKummerRowRoot {a} a (Finset.mem_singleton_self a)) : sixthKummerRowField {a}) : ℂ)=
      ((σ (sixthKummerRowRoot A a ha) : sixthKummerRowField A) : ℂ) := by
  have h := congrArg (fun z : sixthKummerRowField A => (z:ℂ))
    (sixthKummerRowRestriction_commutes A a ha σ
      (sixthKummerRowRoot {a} a (Finset.mem_singleton_self a)))
  rwa [sixthKummerIndividualInclusion_coe,sixthKummerIndividualInclusion_root] at h

theorem sixthKummerRowCharacter_eq_individual_comp {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0) :
    (sixthKummerRowCharacter hζ {a} a (Finset.mem_singleton_self a) ha0).comp
      (sixthKummerRowRestriction A a ha)=sixthKummerRowCharacter hζ A a ha ha0 := by
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  change (((sixthKummerRowRestriction A a ha σ
      (sixthKummerRowRoot {a} a (Finset.mem_singleton_self a)) : sixthKummerRowField {a}) : ℂ) /
      (complexSixthRoot a)) =
    (((σ (sixthKummerRowRoot A a ha) : sixthKummerRowField A) : ℂ) / complexSixthRoot a)
  rw [sixthKummerRowRestriction_root]

end
end ArtinMatthews
