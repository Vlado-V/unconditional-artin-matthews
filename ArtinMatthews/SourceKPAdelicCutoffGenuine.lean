module

public import ArtinMatthews.SourceKPAdelicCuspCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic central character of the global cusp cutoff. -/

namespace ArtinMatthews
open NumberField
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCoverHeight_center (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveCenter K hζ z*q) =
      sourceKPAdelicCoverHeight K hζ q := by
  unfold sourceKPAdelicCoverHeight
  rw [map_mul,sourceKPAdelicProjectiveCenter_projection_one,one_mul]

theorem sourceKPAdelicCutoffSeed_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicCutoffSeed K hζ T s).val (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*(sourceKPAdelicCutoffSeed K hζ T s).val q := by
  change (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ
      (sourceKPAdelicProjectiveCenter K hζ z*q)) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveCenter K hζ z*q) = _
  rw [sourceKPAdelicCoverHeight_center]
  have he := sourceKPAdelicPrincipalSeriesScalar_center K hζ s (sourceKPAdelicCompactSection K hζ s) z q
  change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveCenter K hζ z*q) =
    (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCompactScalar K hζ s q at he
  rw [he]
  change _ * (_ * _) = _ * (_ * _)
  ring

theorem sourceKPAdelicCutoffEisenstein_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffEisenstein K hζ T s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCutoffEisenstein K hζ T s q :=
  sourceKPAdelicRationalSum_genuine K hζ (sourceKPAdelicCutoffSeed K hζ T s)
    (sourceKPAdelicCutoffSeed_center K hζ T s) z q

end
end ArtinMatthews
