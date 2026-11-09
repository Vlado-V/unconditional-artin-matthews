module

public import ArtinMatthews.SourceReflectionExteriorIdele
public import ArtinMatthews.SourceKPFiniteRayRepresentatives
public import ArtinMatthews.IdealRayPrimitiveDescent


set_option backward.privateInPublic true
@[expose] public section

/-! An actual even ideal ray character on an exterior principal ideal is
the inverse character of the retained finite idele. The ray labels are
the original idelic ray-class labels at the character's own modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain RayClass SourcePhysical
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

local notation "n" => integralIdealFiniteModulus M hM
local notation "m" => integralIdealRayModulus M hM

def sourceReflectionRayValue : SourceKPFiniteRayLabels F n →* ℂˣ :=
  (ψ.rayClassCharacter hM).comp (idealRayIdeleQuotientEquiv m).symm.toMonoidHom

def sourceReflectionLocalRayCharacter : SFiniteUnits F S →* ℂˣ :=
  (sourceReflectionRayValue F ψ hM).comp
    ((QuotientGroup.mk' (sourceKPFiniteRaySubgroup F n)).comp (sourceReflectionFiniteIdele F S))

theorem sourceReflectionLocalRayCharacter_apply (u : SFiniteUnits F S) :
    sourceReflectionLocalRayCharacter F S ψ hM u =
      sourceReflectionRayValue F ψ hM
        (sourceKPFiniteRayLabel F n (IdeleGroup.finiteIdeleOfFinset S u)) := rfl

theorem sourceReflectionLocalRayCharacter_finiteOrder :
    ∃ d : ℕ, 0 < d ∧ ∀ u : SFiniteUnits F S, sourceReflectionLocalRayCharacter F S ψ hM u ^ d = 1 := by
  obtain ⟨d,hd,he⟩ := ψ.rayClassCharacter_finiteOrder hM
  exact ⟨d,hd,fun u => he _⟩

theorem sourceReflectionLocalRayCharacter_norm (u : SFiniteUnits F S) :
    ‖(sourceReflectionLocalRayCharacter F S ψ hM u : ℂ)‖ = 1 := by
  obtain ⟨d,hd,he⟩ := sourceReflectionLocalRayCharacter_finiteOrder F S ψ hM
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hd.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z:ℂ)‖) (he u)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using H

theorem sourceReflectionRayValue_idele (a : IdeleGroup F) (ha : a ∈ idelePrimeToModulusSubgroup m) :
    sourceReflectionRayValue F ψ hM (QuotientGroup.mk a) =
      ψ.idealHom (IdeleGroup.fractionalIdeal a) := by
  let b : idelePrimeToModulusSubgroup m := ⟨a,ha⟩
  have hb := idealRayIdeleQuotientEquiv_projection m b
  change idealRayIdeleQuotientEquiv m (idealRayProjection m b) =
    (QuotientGroup.mk a : SourceKPFiniteRayLabels F n) at hb
  change ψ.rayClassCharacter hM ((idealRayIdeleQuotientEquiv m).symm (QuotientGroup.mk a)) = _
  have he := congrArg (idealRayIdeleQuotientEquiv m).symm hb
  calc
    _ = ψ.rayClassCharacter hM (idealRayProjection m b) :=
      congrArg (ψ.rayClassCharacter hM)
        (he.symm.trans ((idealRayIdeleQuotientEquiv m).symm_apply_apply _))
    _ = _ := ψ.rayClassCharacter_ideal hM (primeToIdealMap m b)

theorem sourceReflectionIdealRay_exteriorPrincipal
    (hS : (n).support ⊆ S) (a : Fˣ) :
    ψ.idealHom (IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a)) =
      (sourceReflectionLocalRayCharacter F S ψ hM (sourceReflectionFiniteDiagonal F S a))⁻¹ := by
  let x := sourceReflectionExteriorIdele F S a
  let u := sourceReflectionFiniteDiagonal F S a
  let q := QuotientGroup.mk' (sourceKPFiniteRaySubgroup F n)
  have hx : x ∈ idelePrimeToModulusSubgroup m := by
    refine ⟨?_,?_⟩
    · apply (Modulus.mem_infiniteCongruenceSubgroup_iff m x.1).mpr
      simp [integralIdealRayModulus, Modulus.ofFinite]
    · intro P hP
      change x.2 P ∈ localHigherUnitGroup P (n P)
      rw [sourceReflectionExteriorIdele_apply_mem F S a P (hS hP)]
      exact (localHigherUnitGroup P _).one_mem
  have hp : q (IdeleGroup.principalIdele F a) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.mem_sup_right ⟨a,rfl⟩
  have hq : q x = (q (sourceReflectionFiniteIdele F S u))⁻¹ := by
    change q (IdeleGroup.principalIdele F a / sourceReflectionFiniteIdele F S u) = _
    rw [map_div, hp, one_div]
  calc
    _ = sourceReflectionRayValue F ψ hM (q x) :=
      (sourceReflectionRayValue_idele F ψ hM x hx).symm
    _ = _ := by
      rw [hq, map_inv]
      rfl

end
end ArtinMatthews.VaryingKummerAnalytic
