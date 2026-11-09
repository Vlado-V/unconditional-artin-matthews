module

public import ArtinMatthews.ArtinRayIdeleCorrection
public import ArtinMatthews.ArtinRayConductor


set_option backward.privateInPublic true
@[expose] public section

/-! A small rational congruence produces a genuine norm-class representative
of the principal ideal, by a finite-place power correction. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

theorem degree_pow_ideleClass_mem_norm (B : IdeleGroup K) :
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) B) ^ Module.finrank K L ∈
      (ideleClassNorm K L).range := by
  refine ⟨QuotientGroup.mk' (IdeleGroup.principalSubgroup L)
    (relativeIdeleBaseChangeMulEquiv (K := K) (L := L)
      (RelativeIdeleGroup.inclusion K L B)), ?_⟩
  rw [ideleClassNorm_mk, IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.norm_inclusion, map_pow]

/-- If `D` belongs to each prime in the support of a modulus, then a
generator congruent to one modulo `D*[L:K]²` has a prime-to-modulus idele
representative in the actual idele-class norm range. -/
theorem exists_principal_norm_class_representative
    (m : RayClass.Modulus K) (hm : m.infinitePart = ∅) (D : ℕ)
    (hD : ∀ v ∈ m.finitePart.support, (D : 𝓞 K) ∈ v.asIdeal)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hc : a - 1 ∈ rationalModulusIdeal (𝓞 K) (D * (Module.finrank K L)^2)) :
    ∃ y : RayClass.idelePrimeToModulusSubgroup m,
      (RayClass.primeToIdealMap m y : FractionalIdealGroup K) =
        integralIdealFractionalUnit (Ideal.span {a})
          (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha) ∧
      QuotientGroup.mk' (IdeleGroup.principalSubgroup K) (y : IdeleGroup K) ∈
        (ideleClassNorm K L).range := by
  let x : Kˣ := Units.mk0 (a : K) (by exact_mod_cast ha)
  obtain ⟨B,hB,hcancel⟩ := exists_integral_power_correction m.finitePart.support
    D (Module.finrank K L) Module.finrank_pos hD a ha hc
  let A : IdeleGroup K := IdeleGroup.principalIdele K x * B ^ Module.finrank K L
  have hA : A ∈ RayClass.idelePrimeToModulusSubgroup m := by
    constructor
    · change A.1 ∈ m.infiniteCongruenceSubgroup
      rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
      intro v hv
      simp only [hm, Finset.notMem_empty] at hv
    · intro v hv
      change IdeleGroup.finiteComponent v A ∈ _
      rw [show IdeleGroup.finiteComponent v A = 1 from hcancel v hv]
      exact (RayClass.localHigherUnitGroup v (m.finitePart v)).one_mem
  refine ⟨⟨A,hA⟩, ?_, ?_⟩
  · change IdeleGroup.fractionalIdeal A = _
    dsimp only [A]
    rw [map_mul, map_pow, hB, one_pow, mul_one,
      IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.coeIdeal_span_singleton a).symm
  · have hprincipal : QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
        (IdeleGroup.principalIdele K x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨x,rfl⟩
    change QuotientGroup.mk' (IdeleGroup.principalSubgroup K) A ∈ _
    dsimp only [A]
    rw [map_mul, map_pow, hprincipal]
    exact (ideleClassNorm K L).range.mul_mem (ideleClassNorm K L).range.one_mem
      (degree_pow_ideleClass_mem_norm (L := L) B)

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
