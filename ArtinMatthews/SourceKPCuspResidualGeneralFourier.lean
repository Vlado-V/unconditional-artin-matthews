module

public import ArtinMatthews.SourceKPCuspResidualThetaProfile
public import ArtinMatthews.SourceKPCuspFourierMomentPositive


set_option backward.privateInPublic true
@[expose] public section

/-! Every nonzero rational frequency has an actual residual Fourier
coefficient, defined by one nonzero compact height moment. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups Topology ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ) (m : Kˣ)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
      sourceKPFiniteDeepCoverLift K hζ k)
variable (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K))

def sourceKPCuspResidualCoefficient (c : ℝ≥0) {T : ℝ} (hT : 1 ≤ T) : ℂ :=
  sourceKPCuspNativeFourierResidue K hζ d hd qf (sourceKPCuspHeightBox K)
    (sourceKPCuspHeightBox_isCompact K) (sourceKPCuspHeightBox_positive K) (m:K) hT /
      ((c:ℂ) * sourceKPCuspArchFourierMoment K hζ m (sourceKPCuspHeightBox K) (1/6))

include hperiod hm in
theorem sourceKPCuspResidualFourierCell_integral_eq_general
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in B, sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y
      ∂sourceKPCuspProductHeightMeasure K) =
      sourceKPCuspResidualCoefficient K hζ d hd qf m c hT *
        sourceKPCuspArchFourierMoment K hζ m B (1/6) := by
  have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hA := sourceKPCuspArchFourierMoment_oneSixth_ne_zero K hζ m
  have hcross := sourceKPCuspNativeFourierResidue_cross K hζ d hd qf hperiod m hm
    B (sourceKPCuspHeightBox K) hB (sourceKPCuspHeightBox_isCompact K)
    hpos (sourceKPCuspHeightBox_positive K) hT
  have hI := sourceKPCuspNativeFourierResidue_cell_integral K hζ d hd qf B hB hpos (m:K) hT c hc hmap
  apply mul_right_cancel₀ (mul_ne_zero hcC hA)
  calc
    _ = ((c:ℂ)*(∫ y in B, sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y
          ∂sourceKPCuspProductHeightMeasure K)) *
        sourceKPCuspArchFourierMoment K hζ m (sourceKPCuspHeightBox K) (1/6) := by ring
    _ = sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos (m:K) hT *
        sourceKPCuspArchFourierMoment K hζ m (sourceKPCuspHeightBox K) (1/6) := by rw [← hI]
    _ = sourceKPCuspNativeFourierResidue K hζ d hd qf (sourceKPCuspHeightBox K)
        (sourceKPCuspHeightBox_isCompact K) (sourceKPCuspHeightBox_positive K) (m:K) hT *
        sourceKPCuspArchFourierMoment K hζ m B (1/6) := hcross
    _ = _ := by
      unfold sourceKPCuspResidualCoefficient
      field_simp [hcC,hA]
      <;> ring

include hperiod hm in
theorem sourceKPCuspResidualFourierCell_ae_eq_general
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B]
      fun y => sourceKPCuspResidualCoefficient K hζ d hd qf m c hT *
        sourceKPTraceJacquetArchProfile K hζ m (1/6) y := by
  let a := sourceKPCuspResidualCoefficient K hζ d hd qf m c hT
  let f := sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT
  let g := sourceKPTraceJacquetArchProfile K hζ m (1/6)
  have hf : IntegrableOn f B (sourceKPCuspProductHeightMeasure K) :=
    sourceKPCuspResidualFourierCell_integrableOn K hζ d hd qf B hB hpos (m:K) hT
  have hg : IntegrableOn g B (sourceKPCuspProductHeightMeasure K) :=
    sourceKPCuspArchFourierProfile_integrableOn K hζ d hd m (s := (1/6:ℂ)) (by norm_num) B hB hpos
  have hz : (fun y => f y-a*g y) =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B] 0 := by
    apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero (hf.sub (hg.const_mul a))
    intro S hS
    rw [Measure.restrict_restrict hS.measurableSet]
    have hC : IsCompact (S ∩ B) := hS.inter_right hB.isClosed
    have hp : ∀ y ∈ S ∩ B, ∀ v, 0 < y v := fun y hy => hpos y hy.2
    have hfC := sourceKPCuspResidualFourierCell_integrableOn K hζ d hd qf (S ∩ B) hC hp (m:K) hT
    have hgC := sourceKPCuspArchFourierProfile_integrableOn K hζ d hd m
      (s := (1/6:ℂ)) (by norm_num) (S ∩ B) hC hp
    change (∫ y in S ∩ B,
      sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y -
        a * sourceKPTraceJacquetArchProfile K hζ m (1/6) y
      ∂sourceKPCuspProductHeightMeasure K) = 0
    rw [integral_sub hfC (hgC.const_mul a),integral_const_mul]
    have he := sourceKPCuspResidualFourierCell_integral_eq_general K hζ d hd qf m hperiod hm
      c hc hmap (S ∩ B) hC hp hT
    change (∫ y in S ∩ B, sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y
      ∂sourceKPCuspProductHeightMeasure K) = a *
        (∫ y in S ∩ B, sourceKPTraceJacquetArchProfile K hζ m (1/6) y
          ∂sourceKPCuspProductHeightMeasure K) at he
    exact sub_eq_zero.mpr he
  filter_upwards [hz] with y hy
  exact sub_eq_zero.mp hy

theorem sourceKPCuspResidualFourierCell_has_profile {T : ℝ} (hT : 1 ≤ T) :
    ∃ (e : 𝓞 K) (he : e ≠ 0) (a : ℂ),
      ∀ (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        sourceKPCuspResidualFourierCell K hζ e he qf (m:K) hT =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B]
          fun y => a * sourceKPTraceJacquetArchProfile K hζ m (1/6) y := by
  obtain ⟨e,he,hm',hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (m:K) (1,qf)
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ e he
  refine ⟨e,he,sourceKPCuspResidualCoefficient K hζ e he qf m c hT,?_⟩
  intro B hB hpos
  exact sourceKPCuspResidualFourierCell_ae_eq_general K hζ e he qf m hp hm' c hc hmap B hB hpos hT

end
end ArtinMatthews
