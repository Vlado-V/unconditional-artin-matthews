module

public import ArtinMatthews.SourceKPCompactChartMassLift
public import ArtinMatthews.SourceKPCompactCoreLocalization
public import ArtinMatthews.SourceKPCompactCoreMass
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

/-! The exact finite-isotropy chart measure and the local plateau identity in Haar mass. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "D" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "q" => sourceKPCompactCoordinateProjection K hζ b
local notation "ν" => productVolume (InfinitePlace K)
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactRellichChartMeasure : Measure (ProductSpace (InfinitePlace K)) :=
  (Nat.card H : ℝ≥0∞)⁻¹ • (ν).restrict D

local notation "ρ" => sourceKPCompactRellichChartMeasure K hζ b p

theorem sourceKPCompactRellichChartMeasure_le_restrict : ρ ≤ (ν).restrict D := by
  have hcard : 1 ≤ (Nat.card H : ℝ≥0∞) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.card_pos (α := H))
  have hinv := ENNReal.inv_le_one.mpr hcard
  rw [Measure.le_iff']
  intro s
  rw [sourceKPCompactRellichChartMeasure, Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left (by positivity) hinv

theorem sourceKPCompactRellichChartMeasure_le_volume : ρ ≤ ν :=
  (sourceKPCompactRellichChartMeasure_le_restrict K hζ b p).trans Measure.restrict_le_self

theorem sourceKPCompactRellichChartMeasure_localized_ae (f : sourceKPCompactC2Core K hζ)
    (η : h1LocalTests D) (W : Set Y)
    (hη : ∀ x ∈ D, q x ∈ W → η.val.val =ᶠ[𝓝 x] 1) :
    ∀ᵐ x ∂ρ, q x ∈ W →
      sourceKPCompactCoreMass K hζ 2 f (q x) =
        h1TestMass (sourceKPCompactCoreLocalized K hζ f b p η).val x := by
  have hD : ∀ᵐ x ∂ρ, x ∈ D :=
    ae_mono (sourceKPCompactRellichChartMeasure_le_restrict K hζ b p)
      (ae_restrict_mem (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet)
  have hglobal : (sourceKPCompactCoreMass K hζ 2 f : Y → ℂ) =ᵐ[
      (μ).restrict (Set.range (sourceKPFiniteChartProjection K hζ b p))] f.val :=
    ae_restrict_of_ae (sourceKPCompactCoreMass_coe K hζ f)
  have hm := sourceKPCompactCoordinateProjection_measurePreserving K hζ b p
  have hchart := hm.quasiMeasurePreserving.ae_eq_comp hglobal
  have hlocal := ae_mono (sourceKPCompactRellichChartMeasure_le_volume K hζ b p)
    (h1TestMass_coe (sourceKPCompactCoreLocalized K hζ f b p η).val)
  change ∀ᵐ x ∂ρ, (sourceKPCompactCoreMass K hζ 2 f : Y → ℂ) (q x) = f.val (q x) at hchart
  filter_upwards [hD, hchart, hlocal] with x hx hg hl
  intro hxW
  have hηx : η.val.val x = 1 := (hη x hx hxW).eq_of_nhds
  have hpos := sourceKPFiniteChartCoordinateDomain_upper K hζ b p hx
  rw [hl, sourceKPCompactCoreLocalized_apply, hηx, one_mul,
    sourceKPCompactChartPullback, if_pos hpos]
  exact hg

end
end ArtinMatthews
