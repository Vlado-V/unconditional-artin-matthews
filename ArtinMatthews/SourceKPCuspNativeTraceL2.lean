module

public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspProductMeasure
public import ArtinMatthews.SourceKPCuspNativeFourierTest
public import ArtinMatthews.UnitTorusUnitCellAE
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

/-! Native square integrability gives square integrability on almost every
principal torus slice of a compact positive height band. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "ν" => sourceKPCuspProductHeightMeasure K

theorem sourceKPCuspNativeBand_memLp_product
    (qf : SourceKPFiniteAdeleProjective K hζ) (W : Y → ℂ) (hW : MemLp W 2 μ)
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    MemLp (fun p : (I → ℝ) × (V → ℝ) =>
        W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) (E p)))
      2 ((unitTorusUnitCellMeasure I).prod ((ν).restrict B)) := by
  let S := sourceKPCuspNativeCompactBox K hζ d hd B
  let D := sourceKPCuspNativeBand K hζ d hd B
  let b : SourceKPFiniteLevelFiber K hζ := QuotientGroup.mk qf
  let f : ProductSpace V → ℂ := W ∘ sourceKPCompactCoordinateProjection K hζ b
  let F : (I → ℝ) × (V → ℝ) → ℂ := f ∘ E
  have hS : IsCompact S := sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB
  have hSp : S ⊆ productUpper V := sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos
  have hmem : MemLp (S.indicator f) 2 (productVolume V) := by
    exact MemLp.ae_eq (sourceKPCompactSetMassLift_coe_of_ae K hζ b S hS hSp _ hW.coeFn_toLp)
      (Lp.memLp (sourceKPCompactSetMassLift K hζ b S hS hSp (hW.toLp W)))
  have hs := (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).mp hmem
  have hdLp : MemLp f 2 ((productVolume V).restrict D) := hs.mono_measure
    (Measure.restrict_mono (sourceKPCuspNativeBand_subset_compactBox K hζ d hd B) le_rfl)
  let e := (E).symm.toHomeomorph.toMeasurableEquiv
  have hcomp : F ∘ e = f := by
    funext p
    exact congrArg f ((E).apply_symm_apply p)
  have hm : MemLp F 2 (Measure.map e ((productVolume V).restrict D)) :=
    (e.memLp_map_measure_iff).mpr (hcomp.symm ▸ hdLp)
  obtain ⟨c, hc, hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  have hmap' : Measure.map e ((productVolume V).restrict D) =
      (c : ℝ≥0∞) • (unitTorusUnitCellMeasure I).prod ((ν).restrict B) :=
    sourceKPCuspProductCoordinates_map_restrict_unitCell K hζ d hd c hmap B hB.measurableSet
  rw [hmap'] at hm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hremove := hm.smul_measure (c := (c : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_top.mpr hc0)
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_smul] at hremove
  exact hremove

theorem sourceKPCuspNativeTraceSlice_memLp_ae
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (W : Y → ℂ) (hW : MemLp W 2 μ)
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    ∀ᵐ y ∂(ν).restrict B, ∀ hy : ∀ v, 0 < y v,
      MemLp (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy) 2
        (unitTorusHaar I) := by
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)) := ⟨by simp⟩
  letI : IsFiniteMeasure (unitTorusUnitCellMeasure I) := by
    change IsFiniteMeasure (Measure.pi (fun _ : I => (volume : Measure ℝ).restrict
      (Set.Ioc (0:ℝ) 1)))
    infer_instance
  have h := sourceKPCuspNativeBand_memLp_product K hζ d hd qf W hW B hB hpos
  have hi := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  filter_upwards [h.aestronglyMeasurable.prodMk_right, hi.prod_left_ae] with y hymeas hyint hy
  apply unitTorus_memLp_of_unitCell I
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun x =>
    (sourceKPCuspNativeTraceSlice_unitCell K hζ d hd qf hperiod W y hy x).symm)
    ((memLp_two_iff_integrable_sq_norm hymeas).mpr hyint)

end
end ArtinMatthews
