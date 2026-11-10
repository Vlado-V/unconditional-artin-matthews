module

public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPCompactHeight
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

/-! The band pairing transported to the actual full high quotient. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "π" => sourceKPAutomorphicCompactMk K hζ
local notation "μX" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPAutomorphicBandIntegral_integrable_high (G : Y → ℂ) (hG : Integrable G μY) (T : ℝ) :
    Integrable (fun x : SourceKPHighCuspAutomorphic K hζ T => G (π x.val))
      (sourceKPHighCuspMeasure K hζ T) := by
  have hπ := sourceKPAutomorphicCompactMk_measurePreserving K hζ (sourceKPArchHaar K hζ)
  have hX : Integrable (G ∘ π) μX := hπ.integrable_comp_of_integrable hG
  have hX' : Integrable (G ∘ π) (Measure.map Subtype.val (sourceKPHighCuspMeasure K hζ T)) := by
    rw [sourceKPHighCuspMeasure_map_val]
    exact hX.integrableOn
  have hEmb : MeasurableEmbedding (Subtype.val : SourceKPHighCuspAutomorphic K hζ T → X) :=
    MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  exact hEmb.integrable_map_iff.mp hX'

theorem sourceKPAutomorphicBandIntegral_eq_high (G : Y → ℂ) (hG : Integrable G μY) (T : ℝ)
    (hzero : ∀ y : Y, sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ T → G y = 0) :
    (∫ y : Y, G y ∂μY) =
      ∫ x : SourceKPHighCuspAutomorphic K hζ T, G (π x.val) ∂sourceKPHighCuspMeasure K hζ T := by
  let S : Set X := {x | T < sourceKPAutomorphicOrbitHeight K hζ x}
  have hS : MeasurableSet S := (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  calc
    _ = ∫ x : X, G (π x) ∂μX :=
      integral_map (sourceKPAutomorphicCompactMk_measurable K hζ).aemeasurable hG.aestronglyMeasurable
    _ = ∫ x in S, G (π x) ∂μX := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hHx : sourceKPAutomorphicOrbitHeight K hζ x ≤ T := le_of_not_gt hx
      exact hzero (π x) hHx
    _ = _ := (integral_subtype_comap hS (fun x : X => G (π x))).symm

end
end ArtinMatthews
