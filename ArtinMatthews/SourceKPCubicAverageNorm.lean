module

public import ArtinMatthews.SourceKPCompactGenuineL2
public import ArtinMatthews.SourceKPAdelicUnitNorm
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

/-! Finite Cauchy–Schwarz for the actual cubic character weights. -/
namespace ArtinMatthews
open NumberField
open scoped BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] sourceKPCompactCubicCenter_fintype

theorem sourceKPCubicWeightedAverage_norm_sq_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (v : rootsOfUnity 3 K → V) :
    ‖(3 : ℂ)⁻¹ • ∑ z : rootsOfUnity 3 K,
        (sourceKPAdelicCentralComplex K hζ z : ℂ) • v z‖ ^ 2 ≤
      (3 : ℝ)⁻¹ * ∑ z : rootsOfUnity 3 K, ‖v z‖ ^ 2 := by
  let u : rootsOfUnity 3 K → V := fun z => (sourceKPAdelicCentralComplex K hζ z : ℂ) • v z
  have htriangle : ‖∑ z, u z‖ ≤ ∑ z, ‖v z‖ := by
    simpa only [u, norm_smul, sourceKPAdelicCentralComplex_norm, one_mul] using
      norm_sum_le Finset.univ u
  have hcs : (∑ z, ‖v z‖) ^ 2 ≤ (3 : ℝ) * ∑ z, ‖v z‖ ^ 2 := by
    simpa only [Finset.card_univ, sourceKPCubicCenter_card_three K hζ, Nat.cast_ofNat] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun z => ‖v z‖))
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans hcs
  change ‖(3 : ℂ)⁻¹ • ∑ z, u z‖ ^ 2 ≤ _
  rw [norm_smul, norm_inv, Complex.norm_ofNat, mul_pow]
  calc
    _ ≤ ((3 : ℝ)⁻¹) ^ 2 * ((3 : ℝ) * ∑ z, ‖v z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews
