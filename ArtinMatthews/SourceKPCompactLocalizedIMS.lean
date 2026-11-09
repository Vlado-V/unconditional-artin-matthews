module

public import ArtinMatthews.SourceKPCompactCoreIMS
public import ArtinMatthews.SourceKPCompactExhaustionCore


set_option backward.privateInPublic true
@[expose] public section

/-! Exact form energy of a compact multiplier of a locally smooth weak solution. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff InnerProductSpace Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Ω" => productUpper (InfinitePlace K)
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactCore_localized_ims (w F : Y → ℂ) (hw : Continuous w)
    (hwd : ∀ b, ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ w b) Ω)
    (hweak : ∀ φ : T, ∃ S : Set Y, IsCompact S ∧ ∀ v : T,
      (∀ y ∈ S, v.val =ᶠ[𝓝 y] w) →
        sourceKPCompactDirichletCore K hζ φ v = ∫ y, star (φ.val y)*F y ∂μY)
    (η : T) (hη : ∀ y, (η.val y).im = 0) :
    (∫ y, sourceKPCompactCoreEnergy K hζ (sourceKPCompactCoreMul K hζ η w hw hwd) y ∂μY) =
      (∫ y, star ((η.val y)^2*w y)*F y ∂μY).re +
      ∫ y, ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y ∂μY := by
  let u := sourceKPCompactCoreMul K hζ η w hw hwd
  let η₂ := sourceKPCompactCoreProduct K hζ η η
  let ψ := sourceKPCompactCoreMul K hζ η₂ w hw hwd
  obtain ⟨S,hS,hSweak⟩ := hweak ψ
  obtain ⟨N,hN⟩ := sourceKPAutomorphicExhaustionCutoff_compact_eventually_locally_one K hζ
    (S ∪ tsupport η.val) (hS.union η.prop.2.1)
  let v := sourceKPCompactCoreMul K hζ (sourceKPCompactExhaustionC2 K hζ N) w hw hwd
  have hv (y : Y) (hy : y ∈ S ∪ tsupport η.val) : v.val =ᶠ[𝓝 y] w := by
    filter_upwards [hN N le_rfl y hy] with x hx
    change ((sourceKPAutomorphicExhaustionCutoff K hζ N x : ℝ) : ℂ) * w x = w x
    rw [show sourceKPAutomorphicExhaustionCutoff K hζ N x = 1 from hx,
      Complex.ofReal_one,one_mul]
  have huv : sourceKPCompactCoreProduct K hζ η v = u := by
    apply Subtype.ext
    funext y
    change η.val y*v.val y = η.val y*w y
    by_cases hy : η.val y = 0
    · rw [hy,zero_mul,zero_mul]
    · rw [(hv y (Or.inr (subset_tsupport η.val hy))).eq_of_nhds]
  have hψv : sourceKPCompactCoreProduct K hζ η₂ v = ψ := by
    apply Subtype.ext
    funext y
    change η.val y*η.val y*v.val y = η.val y*η.val y*w y
    by_cases hy : η.val y = 0
    · simp [hy]
    · rw [(hv y (Or.inr (subset_tsupport η.val hy))).eq_of_nhds]
  have hpoint (y : Y) : sourceKPCompactCoreEnergy K hζ u y =
      (sourceKPCompactCorePairDensity K hζ ψ v y).re +
        ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y := by
    have h := sourceKPCompactCoreEnergy_mul_ims K hζ η v hη y
    rw [huv,hψv] at h
    by_cases hy : y ∈ tsupport η.val
    · simpa only [(hv y (Or.inr hy)).eq_of_nhds] using h
    · simpa only [sourceKPCompactCoreEnergy_zero_outside K hζ η hy,mul_zero] using h
  let : IsFiniteMeasureOnCompacts μY := sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  have hI := sourceKPCompactCorePairDensity_integrable K hζ ψ v
  have hR : Integrable (fun y => ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y) μY :=
    ((hw.norm.pow 2).mul (sourceKPCompactCoreEnergy_continuous K hζ η)).integrable_of_hasCompactSupport
      (sourceKPCompactCoreEnergy_hasCompactSupport K hζ η).mul_left
  have hIr : Integrable (fun y => (sourceKPCompactCorePairDensity K hζ ψ v y).re) μY :=
    hI.re
  have hre : (∫ y, (sourceKPCompactCorePairDensity K hζ ψ v y).re ∂μY) =
      (∫ y, sourceKPCompactCorePairDensity K hζ ψ v y ∂μY).re := integral_re hI
  calc
    _ = ∫ y, (sourceKPCompactCorePairDensity K hζ ψ v y).re +
        ‖w y‖^2*sourceKPCompactCoreEnergy K hζ η y ∂μY :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = _ := ?_
  rw [integral_add hIr hR,hre]
  change (sourceKPCompactDirichletCore K hζ ψ v).re+_ = _
  rw [hSweak v (fun y hy => hv y (Or.inl hy))]
  simp only [ψ,η₂,sourceKPCompactCoreProduct_val,sourceKPCompactCoreMul,Pi.mul_apply,pow_two]

end
end ArtinMatthews
