module

public import ArtinMatthews.SourceKPAdelicUnitNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Exact parameter separation of the actual inducing character and
unit-fixed torus vector. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPIdeleComplexNorm_zero (a : IdeleGroup (𝓞 K) K) :
    sourceKPIdeleComplexNorm K 0 a = 1 := by
  apply Units.ext
  rw [sourceKPIdeleComplexNorm_coe, zero_mul, Complex.exp_zero, Units.val_one]

theorem sourceKPIdeleComplexNorm_of_norm_one (s : ℂ) (a : IdeleGroup (𝓞 K) K)
    (ha : sourceKPIdeleAbsoluteNorm K a = 1) : sourceKPIdeleComplexNorm K s a = 1 := by
  apply Units.ext
  rw [sourceKPIdeleComplexNorm_coe, ha, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, Units.val_one]

theorem sourceKPAdelicTorusInducingCharacter_flat (s : ℂ)
    (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    sourceKPAdelicTorusInducingCharacter K hζ s h =
      sourceKPAdelicTorusInducingCharacter K hζ 0 h *
        sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ h.val) := by
  obtain ⟨⟨b,y⟩,hp⟩ := h.property
  change sourceKPAdelicRationalCubeJoin K hζ (b,y) = h.val.val at hp
  obtain ⟨⟨z,c⟩,hq⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective b
  have hc (r : ℂ) : sourceKPAdelicTorusInducingCharacter K hζ r h =
      sourceKPAdelicCentralComplex K hζ z * sourceKPIdeleComplexNorm K r c.val := by
    change sourceKPAdelicParametricRationalCharacter K hζ r
      (⟨h.val.val,h.property⟩ : sourceKPAdelicRationalCubeTorus K hζ) = _
    have he : (⟨sourceKPAdelicRationalCubeJoin K hζ (b,y),⟨(b,y),rfl⟩⟩ :
        sourceKPAdelicRationalCubeTorus K hζ) = ⟨h.val.val,h.property⟩ := Subtype.ext hp
    rw [← he, sourceKPAdelicParametricRationalCharacter_join, ← hq,
      sourceKPAdelicParametricCharacter_equiv]
  have ha : sourceKPAdelicTorusIdele K hζ h.val =
      c.val * IdeleGroup.unitEmbedding (𝓞 K) K y := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    rw [← sourceKPAdelicTorusIdele_projection, ← hp, ← hq,
      sourceKPAdelicCubeRational_join_factor, map_mul,
      sourceKPAdelicProjectiveCenter_projection_one, one_mul,
      sourceKPAdelicProjectiveDiagonalLift_projection]
  rw [hc s, hc 0, sourceKPIdeleComplexNorm_zero, mul_one, ha, map_mul,
    sourceKPIdeleComplexNorm_principal, mul_one]

theorem sourceKPAdelicUnitSphericalVector_flat (s : ℂ)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicUnitSphericalVector K hζ s).val t =
      (sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ t) : ℂ) *
        (sourceKPAdelicUnitSphericalVector K hζ 0).val t := by
  by_cases ht : sourceKPAdelicUnitFactorable K hζ t
  · obtain ⟨h,u,he⟩ := ht
    change sourceKPAdelicUnitSectionValue K hζ s t = _
    rw [sourceKPAdelicUnitSectionValue_factor K hζ s t h u he]
    change (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) =
      (sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ t) : ℂ) *
        sourceKPAdelicUnitSectionValue K hζ 0 t
    rw [sourceKPAdelicUnitSectionValue_factor K hζ 0 t h u he,
      sourceKPAdelicTorusInducingCharacter_flat, Units.val_mul, he, map_mul, map_mul,
      sourceKPIdeleComplexNorm_of_norm_one K s _ (sourceKPAdelicUnitTorus_ideleNorm K hζ u), mul_one]
    exact mul_comm _ _
  · change sourceKPAdelicUnitSectionValue K hζ s t =
      (sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ t) : ℂ) *
        sourceKPAdelicUnitSectionValue K hζ 0 t
    rw [sourceKPAdelicUnitSectionValue_zero K hζ s t ht,
      sourceKPAdelicUnitSectionValue_zero K hζ 0 t ht, mul_zero]

theorem sourceKPAdelicNormalizedBorelVector_flat (s : ℂ) (b : sourceKPAdelicCoveringBorel K hζ) :
    (sourceKPAdelicNormalizedBorelRepresentation K hζ s b
      (sourceKPAdelicUnitSphericalVector K hζ s)).val 1 =
        (sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ
          (sourceKPAdelicBorelTorusProjection K hζ b)) : ℂ) *
        (sourceKPAdelicNormalizedBorelRepresentation K hζ 0 b
          (sourceKPAdelicUnitSphericalVector K hζ 0)).val 1 := by
  change sourceKPAdelicBorelModularHalf K hζ b *
    (sourceKPAdelicUnitSphericalVector K hζ s).val (1*sourceKPAdelicBorelTorusProjection K hζ b) =
      (sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ
        (sourceKPAdelicBorelTorusProjection K hζ b)) : ℂ) *
      (sourceKPAdelicBorelModularHalf K hζ b *
        (sourceKPAdelicUnitSphericalVector K hζ 0).val (1*sourceKPAdelicBorelTorusProjection K hζ b))
  rw [one_mul, sourceKPAdelicUnitSphericalVector_flat]
  ring

end
end ArtinMatthews
