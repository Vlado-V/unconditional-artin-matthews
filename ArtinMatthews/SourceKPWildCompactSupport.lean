module

public import ArtinMatthews.SourceKPDeepAdelicEmbedding
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdeleFiniteKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global compact section has the precise deep-ideal
support on a lower root at a wild finite place. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "q₀" => sourceKPAdelicProjectiveAt K hζ P

def sourceKPAdelicLowerAt (x : L) : SourceKPAdelicProjective K hζ :=
  sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower x))

theorem sourceKPAdelicLowerAt_mem_compact {x : L} (hx : x ∈ sourceKPDeepIdealImage K P) :
    sourceKPAdelicLowerAt K hζ P x ∈ sourceKPAdelicDeepCompact K hζ := by
  obtain ⟨r, hr, rfl⟩ := hx
  have h := sourceKPDeepAdelicMatrix_mem K P hζ (sourceKPDeepLower K P r hr)
  change sourceKPAdelicLocalProjective K hζ P
    (sourceFiniteKP2ProjectiveMk K hζ P
      (sourceKPDeepLocalSection K P hζ (sourceKPDeepLower K P r hr))) ∈ _ at h
  rw [sourceKPDeepLocalSection_lower] at h
  exact h

theorem sourceKPAdelicProjectiveAt_deep_compact (g : sourceKPAdelicDeepCompactMatrix K hζ) :
    q₀ (sourceKPAdelicDeepCompactLift K hζ g) =
      ProjGenLinGroup.mk (sourceKPAdelicBaseFiniteAt K P g.val) := rfl

theorem sourceKPAdelicProjectiveAt_borel (b : sourceKPAdelicCoveringBorel K hζ) :
    ∃ a : sourceGL2NormalizedBorel L, q₀ b.val = ProjGenLinGroup.mk a.val := by
  obtain ⟨a, ha, he⟩ := b.property
  let af := GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K]) a
  let ap := GeneralLinearGroup.map (sourceKPAdeleEval K P) af
  have hap : ap ∈ sourceGL2NormalizedBorel L := by
    constructor
    · change sourceKPAdeleEval K P ((a 1 0).2) = 0
      rw [ha.1]
      exact map_zero _
    · change sourceKPAdeleEval K P ((a 1 1).2) = 1
      rw [ha.2]
      exact map_one _
  refine ⟨⟨ap, hap⟩, ?_⟩
  have hp := congrArg Prod.snd (sourceKPAdelicProjectiveProjection_product K hζ b.val)
  change ProjGenLinGroup.map (RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K])
    (sourceKPAdelicProjectiveProjection K hζ b.val) =
      sourceKPFiniteAdeleProjectiveProjection K hζ b.val.2 at hp
  change ProjGenLinGroup.map (sourceKPAdeleEval K P)
    (sourceKPFiniteAdeleProjectiveProjection K hζ b.val.2) = ProjGenLinGroup.mk ap
  rw [← hp, ← he]
  rfl

theorem sourceKPAdelicLowerAt_factorable_iff (hP : (6 : 𝓞 K) ∈ P.asIdeal) (x : L) :
    sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) (sourceKPAdelicLowerAt K hζ P x) ↔
        x ∈ sourceKPDeepIdealImage K P := by
  constructor
  · rintro ⟨b, k, he⟩
    obtain ⟨g, hg⟩ := k.property
    obtain ⟨kp, hkp⟩ := g.property.2 P hP
    obtain ⟨bp, hbp⟩ := sourceKPAdelicProjectiveAt_borel K hζ P b
    have h := congrArg q₀ he
    change q₀ (sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower x))) = q₀ (b.val * k.val) at h
    rw [map_mul, sourceKPAdelicProjectiveAt_local_same, hbp, ← hg,
      sourceKPAdelicProjectiveAt_deep_compact, ← hkp] at h
    exact (sourceKPDeepLower_projective_iff K P x).mp ⟨bp, kp, h⟩
  · intro hx
    exact ⟨1, ⟨sourceKPAdelicLowerAt K hζ P x, sourceKPAdelicLowerAt_mem_compact K hζ P hx⟩,
      (one_mul _).symm⟩

theorem sourceKPAdelicCompactScalar_lower_mem (s : ℂ) {x : L}
    (hx : x ∈ sourceKPDeepIdealImage K P) :
    sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicLowerAt K hζ P x) = 1 := by
  let k : sourceKPAdelicDeepCompact K hζ :=
    ⟨sourceKPAdelicLowerAt K hζ P x, sourceKPAdelicLowerAt_mem_compact K hζ P hx⟩
  unfold sourceKPAdelicCompactScalar
  rw [sourceKPAdelicCompactSection_factor K hζ s _ 1 k (one_mul _).symm, map_one]
  exact sourceKPAdelicUnitSphericalVector_one K hζ s

end
end ArtinMatthews
