module

public import ArtinMatthews.SourceKPAutomorphicSpectralFamily
public import ArtinMatthews.SourceKPCompactSmoothRepresentative
public import ArtinMatthews.SourceKPResidualChartSmooth
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

/-! The actual exceptional Haar-L² residue has a representative smooth
on every native archimedean chart of the original compact quotient. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Classical ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "Ω" => productUpper V
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "B" => SourceKPFiniteLevelFiber K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "R" => sourceKPAutomorphicExceptionalResidue K hζ

private theorem productVolume_positive_ae :
    ∀ᵐ p ∂productVolume V, p ∈ Ω := by
  have hm := sourceKPArchUpperEuclideanMap_preserving K
  have he : (sourceKPArchUpperEuclideanMap K) ⁻¹' Ω = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p v _
    exact SourceArchJacquet.sourceArchUpperEuclideanMap_positive (p v)
  apply ae_iff.mpr
  change (Measure.pi fun _ : V => OAI.CubicEisenstein.hyperbolicEuclideanVolume) Ωᶜ = 0
  rw [← hm.map_eq, Measure.map_apply hm.measurable (productUpper_isOpen V).measurableSet.compl,
    Set.preimage_compl,he,Set.compl_univ,measure_empty]

theorem sourceKPResidualSmoothRepresentative_exists {T : ℝ} (hT : 1 ≤ T) :
    ∃ W : Y → ℂ, W =ᵐ[μ] (R hT).val ∧
      (∀ b : B, ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPCompactChartPullback K hζ W b) Ω) ∧
      ∀ b : B, sourceKPCompactChartPullback K hζ W b =ᵐ[productVolume V]
        sourceKPCompactChartPullback K hζ ((R hT).val : Y → ℂ) b := by
  classical
  choose U hU hUae using fun b : B => sourceKPResidualChart_smooth_rep K hζ b hT
  obtain ⟨W,hW,hWs,hWe⟩ := sourceKPCompactSmoothRepresentative_exists K hζ
    ((R hT).val : Y → ℂ) U hU hUae
  refine ⟨W,hW,hWs,fun b => ?_⟩
  filter_upwards [productVolume_positive_ae K, hUae b] with p hp hu
  exact (hWe b hp).trans hu

def sourceKPResidualSmoothRepresentative {T : ℝ} (hT : 1 ≤ T) : Y → ℂ :=
  (sourceKPResidualSmoothRepresentative_exists K hζ hT).choose

theorem sourceKPResidualSmoothRepresentative_ae {T : ℝ} (hT : 1 ≤ T) :
    sourceKPResidualSmoothRepresentative K hζ hT =ᵐ[μ] (R hT).val :=
  (sourceKPResidualSmoothRepresentative_exists K hζ hT).choose_spec.1

theorem sourceKPResidualSmoothRepresentative_chart {T : ℝ} (hT : 1 ≤ T) (b : B) :
    ContDiffOn ℝ (∞ : ℕ∞ω)
      (sourceKPCompactChartPullback K hζ (sourceKPResidualSmoothRepresentative K hζ hT) b) Ω :=
  (sourceKPResidualSmoothRepresentative_exists K hζ hT).choose_spec.2.1 b

theorem sourceKPResidualSmoothRepresentative_chart_ae {T : ℝ} (hT : 1 ≤ T) (b : B) :
    sourceKPCompactChartPullback K hζ (sourceKPResidualSmoothRepresentative K hζ hT) b
      =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ ((R hT).val : Y → ℂ) b :=
  (sourceKPResidualSmoothRepresentative_exists K hζ hT).choose_spec.2.2 b

end
end ArtinMatthews
