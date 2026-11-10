module

public import ArtinMatthews.SourceKPCompactFormCoreNorm
public import ArtinMatthews.SourceKPCompactEnergyRegularity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Finite compact-support control for the intrinsic quotient energy. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => SourceKPCompactFormCore K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactCoreEnergy_eq_sub_outside (f g : sourceKPCompactC2Core K hζ)
    (y : Y) (hy : y ∉ tsupport f.val) :
    sourceKPCompactCoreEnergy K hζ g y = sourceKPCompactCoreEnergy K hζ (g-f) y := by
  let D := sourceKPCompactCoreGradientAtLinear K hζ y
  have he := sourceKPCompactCoreGradientAt_norm_sq K hζ f y
  rw [sourceKPCompactCoreEnergy_zero_outside K hζ f hy] at he
  have hf : D f = 0 := by
    apply norm_eq_zero.mp
    change ‖D f‖ ^ 2 = 0 at he
    nlinarith [norm_nonneg (D f)]
  rw [← sourceKPCompactCoreGradientAt_norm_sq,← sourceKPCompactCoreGradientAt_norm_sq]
  change ‖D g‖ ^ 2 = ‖D (g-f)‖ ^ 2
  rw [D.map_sub,hf,sub_zero]

theorem sourceKPCompactCoreEnergy_le_cover {ι : Type*} (f g : T)
    (S : Finset ι) (W : ι → Set Y) (hW : ∀ i ∈ S, MeasurableSet (W i))
    (hcover : tsupport f.val.val ⊆ ⋃ i ∈ S, W i) :
    (∫ y, sourceKPCompactCoreEnergy K hζ g.val y ∂μ) ≤
      ‖g-f‖ ^ 2 + ∑ i ∈ S, ∫ y in W i, sourceKPCompactCoreEnergy K hζ g.val y ∂μ := by
  let E := sourceKPCompactCoreEnergy K hζ g.val
  let D := sourceKPCompactCoreEnergy K hζ (g-f).val
  let J (i : ι) := (W i).indicator E
  have hE := sourceKPCompactCoreEnergy_integrable K hζ g.val
  have hD := sourceKPCompactCoreEnergy_integrable K hζ (g-f).val
  have hJ (i : ι) (hi : i ∈ S) : Integrable (J i) μ := hE.indicator (hW i hi)
  have hJ0 (i : ι) (y : Y) : 0 ≤ J i y := by
    by_cases h : y ∈ W i
    · rw [show J i y = E y from Set.indicator_of_mem h _]
      exact sourceKPCompactCoreEnergy_nonneg K hζ g.val y
    · rw [show J i y = 0 from Set.indicator_of_notMem h _]
  have hp (y : Y) : E y ≤ D y + ∑ i ∈ S, J i y := by
    have h0 : 0 ≤ D y := sourceKPCompactCoreEnergy_nonneg K hζ (g-f).val y
    by_cases hy : y ∈ tsupport f.val.val
    · obtain ⟨i,hi,hyW⟩ := Set.mem_iUnion₂.mp (hcover hy)
      have hi' : J i y ≤ ∑ j ∈ S, J j y :=
        Finset.single_le_sum (fun j _ => hJ0 j y) hi
      have he : J i y = E y := Set.indicator_of_mem hyW _
      rw [he] at hi'
      linarith
    · have he : E y = D y := sourceKPCompactCoreEnergy_eq_sub_outside K hζ f.val g.val y hy
      rw [he]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hJ0 i y))
  have hDnorm : (∫ y, D y ∂μ) ≤ ‖g-f‖ ^ 2 := by
    rw [sourceKPCompactFormCore_norm_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  calc
    _ ≤ ∫ y, D y + ∑ i ∈ S, J i y ∂μ :=
      integral_mono hE (hD.add (integrable_finsetSum S hJ)) hp
    _ = (∫ y, D y ∂μ) + ∑ i ∈ S, ∫ y, J i y ∂μ := by
      rw [integral_add hD (integrable_finsetSum S hJ),integral_finsetSum S hJ]
    _ ≤ _ := by
      apply add_le_add hDnorm
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_eq (integral_indicator (hW i hi))

end
end ArtinMatthews
