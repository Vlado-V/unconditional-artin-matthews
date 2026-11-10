module

public import ArtinMatthews.SourceKPCuspProductMeasure
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

/-! A concrete compact positive-height box has positive finite mass in the
literal hyperbolic height measure. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open scoped ENNReal
noncomputable section

private theorem sourceKPCuspHeightMeasure_Icc :
    sourceKPCuspHeightMeasure (Icc 1 2) =
      ∫⁻ y in Icc (1:ℝ) 2, ENNReal.ofReal ((y^3)⁻¹) ∂volume := by
  rw [sourceKPCuspHeightMeasure,withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hsub : Icc (1:ℝ) 2 ⊆ Ioi (0:ℝ) :=
    fun _ hy => lt_of_lt_of_le zero_lt_one hy.1
  rw [Set.inter_eq_left.mpr hsub]

theorem sourceKPCuspHeightMeasure_Icc_bounds :
    ENNReal.ofReal (1/8:ℝ) ≤ sourceKPCuspHeightMeasure (Icc 1 2) ∧
      sourceKPCuspHeightMeasure (Icc 1 2) ≤ 1 := by
  rw [sourceKPCuspHeightMeasure_Icc]
  have hl : (∫⁻ _y in Icc (1:ℝ) 2, ENNReal.ofReal (1/8:ℝ) ∂volume) ≤
      ∫⁻ y in Icc (1:ℝ) 2, ENNReal.ofReal ((y^3)⁻¹) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
    have hp : y^3 ≤ (8:ℝ) := by nlinarith [pow_le_pow_left₀ hy0.le hy.2 3]
    have hr := one_div_le_one_div_of_le (pow_pos hy0 3) hp
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_div] using hr)
  have hu : (∫⁻ y in Icc (1:ℝ) 2, ENNReal.ofReal ((y^3)⁻¹) ∂volume) ≤
      ∫⁻ _y in Icc (1:ℝ) 2, (1:ℝ≥0∞) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hp : (1:ℝ) ≤ y^3 := by nlinarith [pow_le_pow_left₀ zero_le_one hy.1 3]
    have hr := one_div_le_one_div_of_le zero_lt_one hp
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_div,inv_one] using hr)
  norm_num at hl hu
  exact And.intro hl hu

def sourceKPCuspHeightBox (K : Type) [Field K] [NumberField K] :
    Set (InfinitePlace K → ℝ) :=
  Set.univ.pi (fun _ => Icc (1:ℝ) 2)

theorem sourceKPCuspHeightBox_isCompact (K : Type) [Field K] [NumberField K] :
    IsCompact (sourceKPCuspHeightBox K) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem sourceKPCuspHeightBox_positive (K : Type) [Field K] [NumberField K]
    (y : InfinitePlace K → ℝ) (hy : y ∈ sourceKPCuspHeightBox K) (v : InfinitePlace K) :
    0 < y v :=
  lt_of_lt_of_le zero_lt_one (hy v (mem_univ v)).1

theorem sourceKPCuspHeightBox_mass (K : Type) [Field K] [NumberField K] :
    0 < sourceKPCuspProductHeightMeasure K (sourceKPCuspHeightBox K) ∧
      sourceKPCuspProductHeightMeasure K (sourceKPCuspHeightBox K) < ⊤ := by
  rw [sourceKPCuspProductHeightMeasure,sourceKPCuspHeightBox,Measure.pi_pi]
  constructor
  · apply pos_iff_ne_zero.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ =>
      (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 1/8)) sourceKPCuspHeightMeasure_Icc_bounds.1).ne')
  · apply lt_of_le_of_lt (Finset.prod_le_one (fun _ _ => sourceKPCuspHeightMeasure_Icc_bounds.2))
    exact ENNReal.one_lt_top

end
end ArtinMatthews
