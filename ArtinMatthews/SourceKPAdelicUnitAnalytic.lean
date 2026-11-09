module

public import ArtinMatthews.SourceKPAdelicPrincipalSeries
public import ArtinMatthews.SourceKPAdelicUnitSpherical
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise entire parameter dependence of the actual unit-fixed
inducing vector and its normalized Borel scalar values. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPIdeleComplexNorm_entire (a : IdeleGroup (𝓞 K) K) :
    Differentiable ℂ (fun s : ℂ => (sourceKPIdeleComplexNorm K s a : ℂ)) := by
  change Differentiable ℂ (fun s : ℂ => Complex.exp
    (s * (Real.log (sourceKPIdeleAbsoluteNorm K a) : ℂ)))
  fun_prop

theorem sourceKPAdelicTorusInducingCharacter_entire
    (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    Differentiable ℂ (fun s : ℂ => (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ)) := by
  obtain ⟨⟨b,y⟩, hp⟩ := h.property
  change sourceKPAdelicRationalCubeJoin K hζ (b,y) = h.val.val at hp
  obtain ⟨⟨z,c⟩, hq⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective b
  have he (s : ℂ) : (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) * (sourceKPIdeleComplexNorm K s c.val : ℂ) := by
    change (sourceKPAdelicParametricRationalCharacter K hζ s
      (⟨h.val.val,h.property⟩ : sourceKPAdelicRationalCubeTorus K hζ) : ℂ) = _
    have ht : (⟨sourceKPAdelicRationalCubeJoin K hζ (b,y), ⟨(b,y),rfl⟩⟩ :
        sourceKPAdelicRationalCubeTorus K hζ) = ⟨h.val.val,h.property⟩ := Subtype.ext hp
    rw [← ht, sourceKPAdelicParametricRationalCharacter_join, ← hq,
      sourceKPAdelicParametricCharacter_equiv, Units.val_mul]
  simp_rw [he]
  exact (sourceKPIdeleComplexNorm_entire K c.val).const_mul _

theorem sourceKPAdelicUnitSphericalVector_entire (t : sourceKPAdelicCoveringTorus K hζ) :
    Differentiable ℂ (fun s : ℂ => (sourceKPAdelicUnitSphericalVector K hζ s).val t) := by
  by_cases ht : sourceKPAdelicUnitFactorable K hζ t
  · obtain ⟨h,u,hu⟩ := ht
    have he (s : ℂ) : (sourceKPAdelicUnitSphericalVector K hζ s).val t =
        (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) :=
      sourceKPAdelicUnitSectionValue_factor K hζ s t h u hu
    simp_rw [he]
    exact sourceKPAdelicTorusInducingCharacter_entire K hζ h
  · have he (s : ℂ) : (sourceKPAdelicUnitSphericalVector K hζ s).val t = 0 :=
      sourceKPAdelicUnitSectionValue_zero K hζ s t ht
    simp_rw [he]
    exact differentiable_const (0 : ℂ)

theorem sourceKPAdelicUnitSphericalVector_normalizedBorel_entire
    (b : sourceKPAdelicCoveringBorel K hζ) :
    Differentiable ℂ (fun s : ℂ =>
      (sourceKPAdelicNormalizedBorelRepresentation K hζ s b
        (sourceKPAdelicUnitSphericalVector K hζ s)).val 1) := by
  have he (s : ℂ) :
      (sourceKPAdelicNormalizedBorelRepresentation K hζ s b
        (sourceKPAdelicUnitSphericalVector K hζ s)).val 1 =
      sourceKPAdelicBorelModularHalf K hζ b *
        (sourceKPAdelicUnitSphericalVector K hζ s).val (sourceKPAdelicBorelTorusProjection K hζ b) := by
    change sourceKPAdelicBorelModularHalf K hζ b *
      (sourceKPAdelicUnitSphericalVector K hζ s).val
        (1 * sourceKPAdelicBorelTorusProjection K hζ b) = _
    rw [one_mul]
  simp_rw [he]
  exact (sourceKPAdelicUnitSphericalVector_entire K hζ
    (sourceKPAdelicBorelTorusProjection K hζ b)).const_mul _

end
end ArtinMatthews
