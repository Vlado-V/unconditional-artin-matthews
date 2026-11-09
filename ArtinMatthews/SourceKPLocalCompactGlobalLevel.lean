module

public import ArtinMatthews.SourceKPLocalCompactProjection
public import ArtinMatthews.SourceKPWildCompactSupport
public import ArtinMatthews.SourceKPLocalRestBase


set_option backward.privateInPublic true
@[expose] public section

/-! The local deep lift is the actual one inside the fixed global
compact level. At a wild place its projected image is precisely
the given local deep subgroup. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "G" => SourceKPAdelicProjective K hζ
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "J" => sourceKPLocalCompactDeep K hζ P
local notation "J₀" => sourceKPLocalCompactDeepCoverLevel K hζ P
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "D₀" => sourceKPAdelicDeepCompact K hζ
local notation "q₀" => sourceKPAdelicLocalBase K hζ P

theorem sourceKPLocalCompactDeepCoverLevel_global_mem {g : G₀} (hg : g ∈ J₀) :
    ι₀ g ∈ D₀ := by
  obtain ⟨a,⟨b,rfl⟩,rfl⟩ := hg
  exact sourceKPDeepAdelicMatrix_mem K P hζ b

theorem sourceKPLocalCompactGlobalDeepLevel_projection (hP : (6 : 𝓞 K) ∈ P.asIdeal) :
    (D₀).map q₀ = sourceKPLocalCompactDeepBase K P := by
  ext q
  constructor
  · rintro ⟨g,⟨m,hm⟩,rfl⟩
    obtain ⟨b,hb⟩ := m.property.2 P hP
    rw [← hm]
    change sourceKPAdelicProjectiveAt K hζ P (sourceKPAdelicDeepCompactLift K hζ m) ∈
      sourceKPLocalCompactDeepBase K P
    rw [sourceKPAdelicProjectiveAt_deep_compact K hζ P, ← hb]
    exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    let d := sourceKPDeepProjectiveSection K P hζ b
    refine ⟨ι₀ d,sourceKPDeepAdelicMatrix_mem K P hζ b,?_⟩
    rw [sourceKPAdelicLocalBase_local, sourceKPDeepProjectiveSection_projection] <;> rfl

theorem sourceKPLocalCompactGlobalSection_deep_right (s : ℂ)
    (r : G) (hr : q₀ r = 1) (g : G₀) (j : J) :
    (sourceKPAdelicCompactSection K hζ s).val (ι₀ (g*j.val.val)*r) =
      (sourceKPAdelicCompactSection K hζ s).val (ι₀ g*r) := by
  have hmem := sourceKPLocalCompactDeepCoverLevel_global_mem K hζ P
    (show j.val.val ∈ J₀ from ⟨j.val,j.property,rfl⟩)
  let k : D₀ := ⟨ι₀ j.val.val,hmem⟩
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P j.val.val r hr
  rw [map_mul,mul_assoc,hc.eq,← mul_assoc]
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => f.val (ι₀ g*r))
    (sourceKPAdelicCompactSection_right K hζ s k)

end
end ArtinMatthews
