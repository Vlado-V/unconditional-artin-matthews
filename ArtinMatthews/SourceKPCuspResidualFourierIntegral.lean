module

public import ArtinMatthews.SourceKPCuspNativeFourierTest
public import ArtinMatthews.SourceKPCuspNativeFubini
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable
public import OAI.MathematicalPhysics.BFSS.RellichSmoothing


set_option backward.privateInPublic true
@[expose] public section

/-! The compact native Fourier test of the actual residual L² vector is
the full-dimensional integral of its literal principal-cell Fourier mean. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups Topology ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ

private theorem nativeResidualTest_bound (B : Set (InfinitePlace K → ℝ)) (m : K) :
    ∀ p ∈ sourceKPCuspNativeCompactBox K hζ d hd B,
      ‖sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p‖ ≤ 1 :=
  fun p hp => sourceKPCuspNativeCellTest_bound K hζ d hd m (fun _ => 1) B zero_le_one
    (fun _ _ => by simp) p hp

def sourceKPCuspResidualFourierCell (qf : SourceKPFiniteAdeleProjective K hζ)
    (m : K) {T : ℝ} (hT : 1 ≤ T) (y : InfinitePlace K → ℝ) : ℂ :=
  ∫ x : I → ℝ, star (character K (algebraMap K 𝔸[K] m *
      sourceKPCuspUnitCellAdelicPoint K d hd x)) *
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val
      (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) (E (x,y)))
    ∂unitTorusUnitCellMeasure I

theorem sourceKPCuspNativeFourierResidue_band_integrable
    (qf : SourceKPFiniteAdeleProjective K hζ) (B : Set (InfinitePlace K → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    (m : K) {T : ℝ} (hT : 1 ≤ T) :
    IntegrableOn (fun p : X => star (sourceKPCuspNativeFrequency K hζ d hd m p) *
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val
        (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p))
      (sourceKPCuspNativeBand K hζ d hd B) (productVolume V) := by
  have hi := sourceKPCompactNativeResidueTest_integrableOn K hζ (QuotientGroup.mk qf)
    (sourceKPCuspNativeCompactBox K hζ d hd B)
    (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB)
    (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (nativeResidualTest_bound K hζ d hd B m) hT
  apply (hi.mono_set (sourceKPCuspNativeBand_subset_compactBox K hζ d hd B)).congr
  filter_upwards [ae_restrict_mem (sourceKPCuspNativeBand_measurable K hζ d hd B hB.measurableSet)] with p hp
  rw [sourceKPCuspNativeCellTest,if_pos hp.1,star_one,mul_one]

theorem sourceKPCuspResidualFourierCell_integrableOn
    (qf : SourceKPFiniteAdeleProjective K hζ) (B : Set (InfinitePlace K → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    (m : K) {T : ℝ} (hT : 1 ≤ T) :
    IntegrableOn (sourceKPCuspResidualFourierCell K hζ d hd qf m hT)
      B (sourceKPCuspProductHeightMeasure K) := by
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  letI sourceResidualBaseCellFinite : IsFiniteMeasure
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)) := ⟨by simp⟩
  letI sourceResidualCellFinite : IsFiniteMeasure (unitTorusUnitCellMeasure I) := by
    change IsFiniteMeasure (Measure.pi
      (fun _ : I => (volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)))
    infer_instance
  have hi := sourceKPCuspNativeBand_integrable_product K hζ d hd c hc hmap B hB.measurableSet
    _ (sourceKPCuspNativeFourierResidue_band_integrable K hζ d hd qf B hB hpos m hT)
  have h := hi.integral_prod_right
  change Integrable (fun y => ∫ x : I → ℝ,
    star (character K (algebraMap K 𝔸[K] m * sourceKPCuspUnitCellAdelicPoint K d hd x)) *
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val
        (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) (E (x,y)))
      ∂unitTorusUnitCellMeasure I) ((sourceKPCuspProductHeightMeasure K).restrict B)
  simpa only [sourceKPCuspNativeFrequency_coordinates] using h

theorem sourceKPCuspNativeFourierResidue_band_integral
    (qf : SourceKPFiniteAdeleProjective K hζ) (B : Set (InfinitePlace K → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    (m : K) {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos m hT =
      ∫ p in sourceKPCuspNativeBand K hζ d hd B,
        star (sourceKPCuspNativeFrequency K hζ d hd m p) *
          (sourceKPAutomorphicExceptionalResidue K hζ hT).val
            (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p)
        ∂productVolume V := by
  let f := fun p : X => star (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p) *
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val
      (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p)
  calc
    _ = ∫ p in sourceKPCuspNativeCompactBox K hζ d hd B, f p ∂productVolume V :=
      sourceKPCompactNativeResidueTest_integral K hζ
        (show SourceKPFiniteLevelFiber K hζ from QuotientGroup.mk qf)
        (sourceKPCuspNativeCompactBox K hζ d hd B)
        (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB)
        (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
        (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
        (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
        1 (nativeResidualTest_bound K hζ d hd B m) hT
    _ = ∫ p in sourceKPCuspNativeBand K hζ d hd B, f p ∂productVolume V := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB).measurableSet.nullMeasurableSet
        (sourceKPCuspNativeBand_subset_compactBox K hζ d hd B)
      filter_upwards with p hp
      have hn : ((E).symm p).1 ∉ Set.univ.pi (fun _ : I => Set.Ioc (0:ℝ) 1) := by
        intro hcell
        exact hp.2 ⟨hcell,((sourceKPCuspNativeCompactBox_mem K hζ d hd B p).mp hp.1).2⟩
      simp only [f,sourceKPCuspNativeCellTest,if_neg hn,star_zero,zero_mul]
    _ = _ := by
      apply setIntegral_congr_fun (sourceKPCuspNativeBand_measurable K hζ d hd B hB.measurableSet)
      intro p hp
      simp only [f,sourceKPCuspNativeCellTest,if_pos hp.1,star_one,mul_one]

theorem sourceKPCuspNativeFourierResidue_cell_integral
    (qf : SourceKPFiniteAdeleProjective K hζ) (B : Set (InfinitePlace K → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    (m : K) {T : ℝ} (hT : 1 ≤ T) (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K)) :
    sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos m hT =
      (c:ℂ) * ∫ y in B, sourceKPCuspResidualFourierCell K hζ d hd qf m hT y
        ∂sourceKPCuspProductHeightMeasure K := by
  rw [sourceKPCuspNativeFourierResidue_band_integral]
  rw [sourceKPCuspNativeBand_integral K hζ d hd c hc hmap B hB.measurableSet _
    (sourceKPCuspNativeFourierResidue_band_integrable K hζ d hd qf B hB hpos m hT)]
  simp only [sourceKPCuspResidualFourierCell,sourceKPCuspNativeFrequency_coordinates]

end
end ArtinMatthews
