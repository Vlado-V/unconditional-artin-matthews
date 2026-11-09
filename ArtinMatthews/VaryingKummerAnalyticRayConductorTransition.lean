module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal


set_option backward.privateInPublic true
@[expose] public section

/-! Actual modulus transition in the ideal-theoretic ray class groups.
Surjectivity uses the proved idelic moving equivalence, while the kernel
is identified with genuine principal ideals satisfying the smaller ray
congruence. This is a quotient theorem, not an assumed character descent. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

private theorem finiteModulus_support_mono {m n : Modulus K} (hmn : m ≤ n) :
    m.finitePart.support ⊆ n.finitePart.support := by
  intro v hv
  rw [Finsupp.mem_support_iff] at hv ⊢
  exact ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (hmn.1 v))

def primeToIdealConductorInclusion {m n : Modulus K} (hmn : m ≤ n) :
    primeToModulusIdeals n →* primeToModulusIdeals m :=
  Subgroup.inclusion (by
    intro I hI v hv
    exact hI v (finiteModulus_support_mono hmn hv))

def primeToIdeleConductorInclusion {m n : Modulus K} (hmn : m ≤ n) :
    idelePrimeToModulusSubgroup n →* idelePrimeToModulusSubgroup m :=
  Subgroup.inclusion (by
    intro a ha
    exact ⟨Modulus.infiniteCongruenceSubgroup_antitone hmn ha.1,
      fun v hv => localHigherUnitGroup_antitone v (hmn.1 v)
        (ha.2 v (finiteModulus_support_mono hmn hv))⟩)

def idealRayIdeleQuotientEquiv (m : Modulus K) :
    IdealRayClassGroup m ≃*
      IdeleGroup K ⧸ (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K) :=
  (quotientRaySubgroupEquivIdealRayClassGroup m).symm.trans
    (quotientRaySubgroupEquivIdeleRayQuotient m)

theorem idealRayIdeleQuotientEquiv_projection (m : Modulus K)
    (a : idelePrimeToModulusSubgroup m) :
    idealRayIdeleQuotientEquiv m (idealRayProjection m a) = primeToRayClassProjection m a := by
  rw [← quotientRaySubgroupEquivIdealRayClassGroup_mk m a,
    idealRayIdeleQuotientEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    quotientRaySubgroupEquivIdeleRayQuotient_mk]

private theorem ideleRaySubgroup_mono {m n : Modulus K} (hmn : m ≤ n) :
    n.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K ≤
      m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K :=
  sup_le_sup (Modulus.ideleCongruenceSubgroup_antitone hmn) le_rfl

def ideleConductorProjection {m n : Modulus K} (hmn : m ≤ n) :
    (IdeleGroup K ⧸ (n.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)) →*
      (IdeleGroup K ⧸ (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (ideleRaySubgroup_mono hmn)

theorem ideleConductorProjection_surjective {m n : Modulus K} (hmn : m ≤ n) :
    Function.Surjective (ideleConductorProjection hmn) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ c
  exact ⟨QuotientGroup.mk' _ a, rfl⟩

def idealConductorProjection {m n : Modulus K} (hmn : m ≤ n) :
    IdealRayClassGroup n →* IdealRayClassGroup m :=
  (idealRayIdeleQuotientEquiv m).symm.toMonoidHom.comp
    ((ideleConductorProjection hmn).comp (idealRayIdeleQuotientEquiv n).toMonoidHom)

theorem idealConductorProjection_surjective {m n : Modulus K} (hmn : m ≤ n) :
    Function.Surjective (idealConductorProjection hmn) :=
  (idealRayIdeleQuotientEquiv m).symm.surjective.comp
    ((ideleConductorProjection_surjective hmn).comp
      (idealRayIdeleQuotientEquiv n).surjective)

theorem idealConductorProjection_idele {m n : Modulus K} (hmn : m ≤ n)
    (a : idelePrimeToModulusSubgroup n) :
    idealConductorProjection hmn (idealRayProjection n a) =
      idealRayProjection m (primeToIdeleConductorInclusion hmn a) := by
  apply (idealRayIdeleQuotientEquiv m).injective
  simp only [idealConductorProjection,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,idealRayIdeleQuotientEquiv_projection]
  rfl

theorem idealConductorProjection_ideal {m n : Modulus K} (hmn : m ≤ n)
    (I : primeToModulusIdeals n) :
    idealConductorProjection hmn (QuotientGroup.mk' (principalRayIdealSubgroup n) I) =
      QuotientGroup.mk' (principalRayIdealSubgroup m) (primeToIdealConductorInclusion hmn I) := by
  obtain ⟨a, rfl⟩ := primeToIdealMap_surjective n I
  exact idealConductorProjection_idele hmn a

theorem idealConductorProjection_ideal_eq_one_iff {m n : Modulus K} (hmn : m ≤ n)
    (I : primeToModulusIdeals n) :
    idealConductorProjection hmn (QuotientGroup.mk' (principalRayIdealSubgroup n) I) = 1 ↔
      ∃ x : Kˣ, ∃ _hx : IdeleGroup.principalIdele K x ∈ idelePrimeToModulusSubgroup m,
        toPrincipalIdeal (𝓞 K) K x = (I : FractionalIdealGroup K) := by
  rw [idealConductorProjection_ideal, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_principalRayIdealSubgroup_iff]
  rfl

theorem idealConductorProjection_comp {l m n : Modulus K} (hlm : l ≤ m) (hmn : m ≤ n) :
    (idealConductorProjection hlm).comp (idealConductorProjection hmn) =
      idealConductorProjection (hlm.trans hmn) := by
  apply MonoidHom.ext
  intro c
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  simp only [MonoidHom.comp_apply,idealConductorProjection_ideal]
  rfl

end
end ArtinMatthews.VaryingKummerAnalytic
