module

public import ArtinMatthews.SourceKPAdelicTranslatedHeight
public import ArtinMatthews.SourceKPAdelicHeightFactor


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Borel covariance and compact invariance of the actual
adelic Iwasawa height. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_left_borel (b g : GL (Fin 2) 𝔸[K])
    (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K]) :
    sourceKPAdelicHeight K hζ (b*g) =
      sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det b) * sourceKPAdelicHeight K hζ g := by
  have hbg : b * sourceKPAdelicIwasawaBorel K hζ g ∈ sourceKPRingNormalizedBorel 𝔸[K] :=
    (sourceKPRingNormalizedBorel 𝔸[K]).mul_mem hb (sourceKPAdelicIwasawaBorel_mem K hζ g)
  have he : b*g = (b*sourceKPAdelicIwasawaBorel K hζ g) *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicIwasawaScalar K hζ g) *
        sourceKPAdelicIwasawaCompact K hζ g := by
    conv_lhs => rw [sourceKPAdelicIwasawa_factor K hζ g]
    group
  rw [sourceKPAdelicHeight_factor K hζ _ _ _ _ hbg
    (sourceKPAdelicIwasawaCompact_mem K hζ g) he, map_mul, map_mul]
  rfl

theorem sourceKPAdelicHeight_right_baseCompact (g k : GL (Fin 2) 𝔸[K])
    (hk : k ∈ SourceKPAdelicBaseCompactMatrix K hζ) :
    sourceKPAdelicHeight K hζ (g*k) = sourceKPAdelicHeight K hζ g := by
  have hk' : sourceKPAdelicIwasawaCompact K hζ g * k ∈ SourceKPAdelicBaseCompactMatrix K hζ :=
    (SourceKPAdelicBaseCompactMatrix K hζ).mul_mem (sourceKPAdelicIwasawaCompact_mem K hζ g) hk
  have he : g*k = sourceKPAdelicIwasawaBorel K hζ g *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicIwasawaScalar K hζ g) *
        (sourceKPAdelicIwasawaCompact K hζ g*k) := by
    conv_lhs => rw [sourceKPAdelicIwasawa_factor K hζ g]
    group
  exact sourceKPAdelicHeight_factor K hζ _ _ _ _
    (sourceKPAdelicIwasawaBorel_mem K hζ g) hk' he

theorem sourceKPAdelicHeight_left_rationalBorel (b : GL (Fin 2) K)
    (hb : b ∈ sourceKPRingNormalizedBorel K) (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ (GeneralLinearGroup.map (algebraMap K 𝔸[K]) b*g) =
      sourceKPAdelicHeight K hζ g := by
  have hb' : GeneralLinearGroup.map (algebraMap K 𝔸[K]) b ∈ sourceKPRingNormalizedBorel 𝔸[K] := by
    constructor
    · change algebraMap K 𝔸[K] (b 1 0) = 0
      rw [hb.1, map_zero]
    · change algebraMap K 𝔸[K] (b 1 1) = 1
      rw [hb.2, map_one]
  rw [sourceKPAdelicHeight_left_borel K hζ _ g hb', GeneralLinearGroup.map_det]
  change sourceKPIdeleAbsoluteNorm K (IdeleGroup.unitEmbedding (𝓞 K) K
    (GeneralLinearGroup.det b)) * sourceKPAdelicHeight K hζ g = _
  rw [sourceKPIdeleAbsoluteNorm_principal, one_mul]

end
end ArtinMatthews
