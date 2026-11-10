module

public import ArtinMatthews.SourceKPFiniteChartAverage
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceHyperbolicH1Measure
public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPFiniteChartCoordinateMeasure
public import ArtinMatthews.SourceKPGlobalChartMeasure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
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


set_option backward.privateInPublic true
@[expose] public section

/-! Localized scalar Haar mass pulled back to each true finite-isotropy coordinate chart. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "R" => Set.range (sourceKPFiniteChartProjection K hζ b p)
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)

def sourceKPCompactCoordinateProjection (x : X) : Y :=
  sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x)

theorem sourceKPCompactCoordinateProjection_measurable :
    Measurable (sourceKPCompactCoordinateProjection K hζ b) :=
  (sourceKPUpperToCompact_continuous K hζ b).measurable.comp
    (sourceKPArchEuclideanUpperMap_preserving K).measurable

theorem sourceKPCompactCoordinateProjection_measurePreserving :
    MeasurePreserving (sourceKPCompactCoordinateProjection K hζ b)
      ((Nat.card H : ℝ≥0∞)⁻¹ • (ν).restrict U) ((μ).restrict R) := by
  let c := sourceKPUpperFiniteChart K hζ b p
  let m := sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K)
  let e : c.domain → X := fun x => sourceKPArchUpperEuclideanMap K x.val
  let q := sourceKPCompactCoordinateProjection K hζ b
  have he := sourceKPFiniteChartCoordinates_measurePreserving K hζ b p
  have hq := sourceKPCompactCoordinateProjection_measurable K hζ b
  have heq : q ∘ e = sourceKPFiniteChartProjection K hζ b p := by
    funext x
    change sourceKPUpperToCompact K hζ b
      (sourceKPArchEuclideanUpperMap K (sourceKPArchUpperEuclideanMap K x.val)) = _
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    rfl
  refine ⟨hq,?_⟩
  change Measure.map q ((Nat.card H : ℝ≥0∞)⁻¹ • (ν).restrict U) = _
  rw [← he.map_eq,← Measure.map_smul _ he.measurable.aemeasurable,
    Measure.map_map hq he.measurable,heq]
  exact (sourceKPFiniteChartProjection_measurePreserving K hζ b p).map_eq

theorem sourceKPCompactChartMassLift_memLp (g : Lp ℂ 2 μ) :
    MemLp ((U).indicator (g ∘ sourceKPCompactCoordinateProjection K hζ b)) 2 ν := by
  let q := sourceKPCompactCoordinateProjection K hζ b
  have hu := (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet
  have hw : MemLp (g ∘ q) 2 ((Nat.card H : ℝ≥0∞)⁻¹ • (ν).restrict U) :=
    ((Lp.memLp g).mono_measure Measure.restrict_le_self).comp_measurePreserving
      (sourceKPCompactCoordinateProjection_measurePreserving K hζ b p)
  have hn : (Nat.card H : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card H ≠ 0)
  have huLp := hw.smul_measure (c := (Nat.card H : ℝ≥0∞)) (ENNReal.natCast_ne_top _)
  rw [smul_smul,ENNReal.mul_inv_cancel hn (ENNReal.natCast_ne_top _),one_smul] at huLp
  exact (memLp_indicator_iff_restrict hu.nullMeasurableSet).mpr huLp

def sourceKPCompactChartMassLift (g : Lp ℂ 2 μ) : SourceKPFiniteChartMass K hζ b p := by
  let h := sourceKPCompactChartMassLift_memLp K hζ b p g
  refine ⟨h.toLp _,?_⟩
  filter_upwards [h.coeFn_toLp] with x hx hxu
  rw [hx,Set.indicator_of_notMem hxu]

theorem sourceKPCompactChartMassLift_coe (g : Lp ℂ 2 μ) :
    ((sourceKPCompactChartMassLift K hζ b p g).val : X → ℂ) =ᵐ[ν]
      (U).indicator (g ∘ sourceKPCompactCoordinateProjection K hζ b) :=
  (sourceKPCompactChartMassLift_memLp K hζ b p g).coeFn_toLp

theorem sourceKPCompactChartMassLift_invariant (g : Lp ℂ 2 μ) (γ : H) :
    sourceKPFiniteChartMassPullback K hζ b p γ (sourceKPCompactChartMassLift K hζ b p g) =
      sourceKPCompactChartMassLift K hζ b p g := by
  let f := (sourceKPCompactChartMassLift K hζ b p g).val
  let a := sourceKPArchEuclideanAction K hζ γ.val.val
  let m := sourceKPArchEuclideanAction_preserving K hζ γ.val.val
  let q := sourceKPCompactCoordinateProjection K hζ b
  apply Subtype.ext
  change Lp.compMeasurePreserving a m f = f
  apply Lp.ext
  have he := sourceKPCompactChartMassLift_coe K hζ b p g
  filter_upwards [Lp.coeFn_compMeasurePreserving f m,he,
    m.quasiMeasurePreserving.ae he,productVolume_ae_upper (ι := InfinitePlace K)] with x h1 h2 h3 hpos
  change (Lp.compMeasurePreserving a m f) x = f x
  rw [h1]
  change f (a x) = f x
  rw [h3,h2]
  have hmem : a x ∈ U ↔ x ∈ U := by
    refine ⟨?_,sourceKPFiniteChartCoordinateDomain_invariant K hζ b p γ⟩
    intro hx
    have h := sourceKPFiniteChartCoordinateDomain_invariant K hζ b p γ⁻¹ hx
    change sourceKPArchEuclideanAction K hζ (γ.val.val)⁻¹ (a x) ∈ U at h
    change sourceKPArchEuclideanAction K hζ (γ.val.val)⁻¹
      (sourceKPArchEuclideanAction K hζ γ.val.val x) ∈ U at h
    rw [← sourceKPArchEuclideanAction_mul,inv_mul_cancel,
      sourceKPArchEuclideanAction_one K hζ x hpos] at h
    exact h
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (hmem.mpr hx)]
    apply congrArg g
    change q (a x) = q x
    unfold q a sourceKPCompactCoordinateProjection sourceKPArchEuclideanAction
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    exact sourceKPUpperToCompact_smul K hζ b γ.val (sourceKPArchEuclideanUpperMap K x)
  · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (hmem.not.mpr hx)]

end
end ArtinMatthews
