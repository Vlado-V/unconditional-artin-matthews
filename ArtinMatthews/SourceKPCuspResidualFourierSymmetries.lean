module

public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPCubicUpperAction


set_option backward.privateInPublic true
@[expose] public section

/-! The literal compact Fourier test respects the deep right level and
the forward cubic character of the genuine residue. -/
namespace ArtinMatthews

open NumberField Matrix MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing NNReal ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V

theorem sourceKPCuspResidualFourierValue_right_level
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf k : Gf)
    (hk : k ∈ sourceKPFiniteLevelSubgroup K hζ) :
    sourceKPCuspResidualFourierValue K hζ m hT (qf*k) =
      sourceKPCuspResidualFourierValue K hζ m hT qf := by
  let g : Bool → SourceKPAdelicProjective K hζ
    | false => (1,qf)
    | true => (1,qf*k)
  obtain ⟨d,hd,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod_common K hζ (m:K) g
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  rw [sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT (qf*k) d hd c hc (hp true) hm hmap,
    sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT qf d hd c hc (hp false) hm hmap]
  unfold sourceKPCuspResidualCoefficient sourceKPCuspNativeFourierResidue
  rw [show (QuotientGroup.mk (qf*k) : F) = QuotientGroup.mk qf from QuotientGroup.mk_mul_of_mem qf hk]

theorem sourceKPCuspResidualFourierValue_right_deep
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPCuspResidualFourierValue K hζ m hT (qf * sourceKPFiniteLevelLift K hζ k) =
      sourceKPCuspResidualFourierValue K hζ m hT qf :=
  sourceKPCuspResidualFourierValue_right_level K hζ m hT qf _ ⟨k,rfl⟩

theorem sourceKPCuspResidualFourierValue_center
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (z : rootsOfUnity 3 K) :
    sourceKPCuspResidualFourierValue K hζ m hT (sourceKPFiniteAdeleProjectiveCenter K hζ z * qf) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        sourceKPCuspResidualFourierValue K hζ m hT qf := by
  let Q := sourceKPFiniteAdeleProjectiveCenter K hζ z * qf
  let g : Bool → SourceKPAdelicProjective K hζ
    | false => (1,qf)
    | true => (1,Q)
  obtain ⟨d,hd,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod_common K hζ (m:K) g
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  let B := sourceKPCuspHeightBox K
  let hB := sourceKPCuspHeightBox_isCompact K
  let hbpos := sourceKPCuspHeightBox_positive K
  let S := sourceKPCuspNativeBand K hζ d hd B
  let S' := sourceKPCuspNativeCompactBox K hζ d hd B
  let q (b : Gf) := sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk b)
  let R := sourceKPAutomorphicExceptionalResidue K hζ hT
  let χ := (sourceKPAdelicCentralComplex K hζ z : ℂ)
  let φ (p : X) := star (sourceKPCuspNativeFrequency K hζ d hd (m:K) p)
  have hR : ∀ᵐ y ∂μY, R.val (z • y) = χ * R.val y :=
    ((sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ) R.val).mp R.prop) z
  have hq (p : X) : q Q p = z • q qf p :=
    (sourceKPCubicCenter_upperToCompact K hζ z (show F from QuotientGroup.mk qf)
      (sourceKPArchEuclideanUpperMap K p)).symm
  have hnative : ∀ᵐ p ∂productVolume V, p ∈ S' → R.val (z • q qf p) = χ * R.val (q qf p) :=
    sourceKPCompactCoordinateProjection_ae_compact K hζ (QuotientGroup.mk qf) S'
      (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB)
      (sourceKPCuspNativeCompactBox_positive K hζ d hd B hbpos) hR
  let res (b : Gf) := sourceKPCuspNativeFourierResidue K hζ d hd b B hB hbpos (m:K) hT
  have hres (b : Gf) : res b = ∫ p in S, φ p * R.val (q b p) ∂productVolume V :=
    sourceKPCuspNativeFourierResidue_band_integral K hζ d hd b B hB hbpos (m:K) hT
  have he : res Q = χ * res qf := by
    rw [hres Q, hres qf, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hnative,
      ae_restrict_mem (sourceKPCuspNativeBand_measurable K hζ d hd B hB.measurableSet)] with p hp' hp
    rw [hq, hp' (sourceKPCuspNativeBand_subset_compactBox K hζ d hd B hp)]
    ring
  rw [sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT Q d hd c hc (hp true) hm hmap,
    sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT qf d hd c hc (hp false) hm hmap]
  change res Q / ((c:ℂ) * sourceKPCuspArchFourierMoment K hζ m B (1/6)) =
    χ * (res qf / ((c:ℂ) * sourceKPCuspArchFourierMoment K hζ m B (1/6)))
  rw [he, mul_div_assoc]

end
end ArtinMatthews
