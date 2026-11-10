module

public import ArtinMatthews.PrimeExtractionRelevantBoxes
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

/-! The selected actual dyadic boxes have a fixed positive power lower
bound on each endpoint, as required by Proposition 2.1. -/

namespace ArtinMatthews

open Filter

theorem prime_extraction_half_power_le_eventually {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, x ^ (γ/2) ≤ x ^ γ / 2 := by
  filter_upwards [(tendsto_rpow_atTop (by linarith : 0 < γ/2)).eventually
    (eventually_ge_atTop (2 : ℝ)), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have heq : x ^ γ = x ^ (γ/2) * x ^ (γ/2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [heq]
  nlinarith

theorem primeExtractionRelevantBoxes_geometry_eventually {a T γ : ℝ}
    (hT : 0 ≤ T) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
      a*x/4 ≤ primeExtractionDyadicHeight kl.1 kl.2 ∧
        primeExtractionDyadicHeight kl.1 kl.2 ≤ T*x ∧
        x^(γ/2) ≤ (2 : ℝ)^kl.1 ∧ x^(γ/2) ≤ (2 : ℝ)^kl.2 := by
  filter_upwards [prime_extraction_half_power_le_eventually hγ,
    eventually_ge_atTop (0 : ℝ)] with x hx hx0
  intro kl hkl
  have hg := primeExtractionRelevantBoxes_geometry (Nat.floor_le (mul_nonneg hT hx0)) hkl
  exact ⟨hg.1, hg.2.1, hx.trans hg.2.2.1.le, hx.trans hg.2.2.2.le⟩

end ArtinMatthews
