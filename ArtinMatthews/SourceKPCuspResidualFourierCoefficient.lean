module

public import ArtinMatthews.SourceKPCuspResidualFourierIntegral
public import ArtinMatthews.SourceKPCuspResidueFourierMoments
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed full-dimensional compact test defines the actual residual
unit-frequency coefficient. Its normalized Bessel profile holds almost
everywhere on every compact positive height set. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups Topology ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
variable (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
      sourceKPFiniteDeepCoverLift K hζ k)

def sourceKPCuspResidualUnitCoefficient (c : ℝ≥0) {T : ℝ} (hT : 1 ≤ T) : ℂ :=
  sourceKPCuspNativeFourierResidue K hζ d hd qf (sourceKPCuspHeightBox K)
    (sourceKPCuspHeightBox_isCompact K) (sourceKPCuspHeightBox_positive K) (1:K) hT /
      ((c:ℂ) * sourceKPCuspUnitArchMoment K (1/6))

include hperiod in
theorem sourceKPCuspResidualFourierCell_integral_eq
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in B, sourceKPCuspResidualFourierCell K hζ d hd qf (1:K) hT y
      ∂sourceKPCuspProductHeightMeasure K) =
      sourceKPCuspResidualUnitCoefficient K hζ d hd qf c hT *
        sourceKPCuspArchFourierMoment K hζ (1:Kˣ) B (1/6) := by
  have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hA := sourceKPCuspUnitArchMoment_oneSixth_ne_zero K
  apply mul_left_cancel₀ hcC
  calc
    _ = sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos (1:K) hT :=
      (sourceKPCuspNativeFourierResidue_cell_integral K hζ d hd qf B hB hpos (1:K) hT c hc hmap).symm
    _ = _ := sourceKPCuspNativeFourierResidue_unit_normalized K hζ d hd qf hperiod B hB hpos hT
    _ = _ := by
      unfold sourceKPCuspResidualUnitCoefficient
      field_simp [hcC,hA]
      <;> ring

include hperiod in
theorem sourceKPCuspResidualFourierCell_ae_eq
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspResidualFourierCell K hζ d hd qf (1:K) hT =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B]
      fun y => sourceKPCuspResidualUnitCoefficient K hζ d hd qf c hT *
        sourceKPTraceJacquetArchProfile K hζ (1:Kˣ) (1/6) y := by
  let a := sourceKPCuspResidualUnitCoefficient K hζ d hd qf c hT
  let f := sourceKPCuspResidualFourierCell K hζ d hd qf (1:K) hT
  let g := sourceKPTraceJacquetArchProfile K hζ (1:Kˣ) (1/6)
  have hf : IntegrableOn f B (sourceKPCuspProductHeightMeasure K) :=
    sourceKPCuspResidualFourierCell_integrableOn K hζ d hd qf B hB hpos (1:K) hT
  have hg : IntegrableOn g B (sourceKPCuspProductHeightMeasure K) :=
    sourceKPCuspArchFourierProfile_integrableOn K hζ d hd (1:Kˣ) (s := (1/6:ℂ)) (by norm_num) B hB hpos
  have hz : (fun y => f y-a*g y) =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B] 0 := by
    apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero (hf.sub (hg.const_mul a))
    intro S hS
    rw [Measure.restrict_restrict hS.measurableSet]
    have hC : IsCompact (S ∩ B) := hS.inter_right hB.isClosed
    have hp : ∀ y ∈ S ∩ B, ∀ v, 0 < y v := fun y hy => hpos y hy.2
    have hfC := sourceKPCuspResidualFourierCell_integrableOn K hζ d hd qf (S ∩ B) hC hp (1:K) hT
    have hgC := sourceKPCuspArchFourierProfile_integrableOn K hζ d hd (1:Kˣ) (s := (1/6:ℂ)) (by norm_num) (S ∩ B) hC hp
    change (∫ y in S ∩ B,
      sourceKPCuspResidualFourierCell K hζ d hd qf (1:K) hT y -
        a * sourceKPTraceJacquetArchProfile K hζ (1:Kˣ) (1/6) y
      ∂sourceKPCuspProductHeightMeasure K) = 0
    rw [integral_sub hfC (hgC.const_mul a),integral_const_mul]
    have he := sourceKPCuspResidualFourierCell_integral_eq K hζ d hd qf hperiod c hc hmap
      (S ∩ B) hC hp hT
    change (∫ y in S ∩ B, sourceKPCuspResidualFourierCell K hζ d hd qf (1:K) hT y
      ∂sourceKPCuspProductHeightMeasure K) = a *
        (∫ y in S ∩ B, sourceKPTraceJacquetArchProfile K hζ (1:Kˣ) (1/6) y
          ∂sourceKPCuspProductHeightMeasure K) at he
    exact sub_eq_zero.mpr he
  filter_upwards [hz] with y hy
  exact sub_eq_zero.mp hy

theorem sourceKPCuspResidualFourierCell_has_unit_profile {T : ℝ} (hT : 1 ≤ T) :
    ∃ (e : 𝓞 K) (he : e ≠ 0) (a : ℂ),
      ∀ (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        sourceKPCuspResidualFourierCell K hζ e he qf (1:K) hT =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B]
          fun y => a * sourceKPTraceJacquetArchProfile K hζ (1:Kˣ) (1/6) y := by
  obtain ⟨e,he,_,hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (1:K) (1,qf)
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ e he
  refine ⟨e,he,sourceKPCuspResidualUnitCoefficient K hζ e he qf c hT,?_⟩
  intro B hB hpos
  exact sourceKPCuspResidualFourierCell_ae_eq K hζ e he qf hp c hc hmap B hB hpos hT

end
end ArtinMatthews
