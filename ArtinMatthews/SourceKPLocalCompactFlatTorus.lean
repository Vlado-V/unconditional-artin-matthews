module

public import ArtinMatthews.SourceKPAdelicFlatTorus
public import ArtinMatthews.SourceKPAdelicCompactSection


set_option backward.privateInPublic true
@[expose] public section

/-! Exact linear trivialization of the genuine parameter-dependent
adelic torus value spaces. It preserves all global support and
central data. The scalar twist of any Borel action is explicit. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped AdeleRing NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "H" => sourceKPAdelicTorusInducingSubgroup K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ

def sourceKPLocalCompactTorusNorm (s : ℂ) : T →* ℂˣ :=
  (sourceKPIdeleComplexNorm K s).comp (sourceKPAdelicTorusIdele K hζ)

local notation "α" => sourceKPLocalCompactTorusNorm K hζ

private theorem sourceKPLocalCompactTorusCharacter_flat (s : ℂ) (h : H) :
    (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) =
      (sourceKPAdelicTorusInducingCharacter K hζ 0 h : ℂ)*(α s h.val : ℂ) := by
  rw [sourceKPAdelicTorusInducingCharacter_flat K hζ s h]
  rfl

def sourceKPLocalCompactTorusFlatEquiv (s : ℂ) : V 0 ≃ₗ[ℂ] V s where
  toFun v := ⟨fun t => (α s t : ℂ)*v.val t, by
    intro h t
    change (α s (h.val*t) : ℂ)*v.val (h.val*t) =
      (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ)*((α s t : ℂ)*v.val t)
    rw [map_mul,Units.val_mul,sourceAlgebraicInducedSpace_covariant _ _ v h,
      sourceKPAdelicTorusInducingRepresentation_apply,sourceKPLocalCompactTorusCharacter_flat K hζ s h]
    ring⟩
  invFun v := ⟨fun t => (α s t : ℂ)⁻¹*v.val t, by
    intro h t
    change (α s (h.val*t) : ℂ)⁻¹*v.val (h.val*t) =
      (sourceKPAdelicTorusInducingCharacter K hζ 0 h : ℂ)*((α s t : ℂ)⁻¹*v.val t)
    rw [map_mul,Units.val_mul,mul_inv_rev,sourceAlgebraicInducedSpace_covariant _ _ v h,
      sourceKPAdelicTorusInducingRepresentation_apply,sourceKPLocalCompactTorusCharacter_flat K hζ s h]
    field_simp [Units.ne_zero (α s h.val),Units.ne_zero (α s t)]⟩
  left_inv v := by
    apply Subtype.ext
    funext t
    change (α s t : ℂ)⁻¹*((α s t : ℂ)*v.val t) = v.val t
    rw [← mul_assoc,inv_mul_cancel₀ (Units.ne_zero (α s t)),one_mul]
  right_inv v := by
    apply Subtype.ext
    funext t
    change (α s t : ℂ)*((α s t : ℂ)⁻¹*v.val t) = v.val t
    rw [← mul_assoc,mul_inv_cancel₀ (Units.ne_zero (α s t)),one_mul]
  map_add' v w := by
    apply Subtype.ext
    funext t
    exact mul_add _ _ _
  map_smul' a v := by
    apply Subtype.ext
    funext t
    change (α s t : ℂ)*(a*v.val t) = a*((α s t : ℂ)*v.val t)
    ring

theorem sourceKPLocalCompactTorusFlatEquiv_apply (s : ℂ) (v : V 0) (t : T) :
    (sourceKPLocalCompactTorusFlatEquiv K hζ s v).val t = (α s t : ℂ)*v.val t := rfl

theorem sourceKPLocalCompactTorusFlatEquiv_action (s : ℂ)
    (b : sourceKPAdelicCoveringBorel K hζ) (v : V 0) :
    ρ s b (sourceKPLocalCompactTorusFlatEquiv K hζ s v) =
      (α s (sourceKPAdelicBorelTorusProjection K hζ b) : ℂ) •
        sourceKPLocalCompactTorusFlatEquiv K hζ s (ρ 0 b v) := by
  apply Subtype.ext
  funext t
  let d := sourceKPAdelicBorelTorusProjection K hζ b
  let δ := sourceKPAdelicBorelModularHalf K hζ b
  change δ*((α s (t*d) : ℂ)*v.val (t*d)) =
    (α s d : ℂ)*((α s t : ℂ)*(δ*v.val (t*d)))
  rw [map_mul,Units.val_mul]
  ring

theorem sourceKPLocalCompactTorusFlatEquiv_spherical (s : ℂ) :
    sourceKPLocalCompactTorusFlatEquiv K hζ s (sourceKPAdelicUnitSphericalVector K hζ 0) =
      sourceKPAdelicUnitSphericalVector K hζ s := by
  apply Subtype.ext
  funext t
  exact (sourceKPAdelicUnitSphericalVector_flat K hζ s t).symm

theorem sourceKPLocalCompactSection_flat (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    ∃ c : ℂˣ, (sourceKPAdelicCompactSection K hζ s).val g =
      (c : ℂ) • sourceKPLocalCompactTorusFlatEquiv K hζ s
        ((sourceKPAdelicCompactSection K hζ 0).val g) := by
  by_cases h : sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) g
  · obtain ⟨b,k,hg⟩ := h
    refine ⟨α s (sourceKPAdelicBorelTorusProjection K hζ b),?_⟩
    rw [sourceKPAdelicCompactSection_factor K hζ s g b k hg,
      sourceKPAdelicCompactSection_factor K hζ 0 g b k hg,
      ← sourceKPLocalCompactTorusFlatEquiv_spherical K hζ s,
      sourceKPLocalCompactTorusFlatEquiv_action K hζ s b]
  · have hz (r : ℂ) : (sourceKPAdelicCompactSection K hζ r).val g = 0 :=
      sourceCompactInducedValue_zero _ _ _ _ h
    have he : sourceKPLocalCompactTorusFlatEquiv K hζ s (0 : V 0) = (0 : V s) :=
      (sourceKPLocalCompactTorusFlatEquiv K hζ s).toLinearMap.map_zero
    exact ⟨1,by rw [hz s,hz 0,he,smul_zero]⟩

end
end ArtinMatthews
