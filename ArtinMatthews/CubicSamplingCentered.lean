module

public import ArtinMatthews.CubicSamplingBaselineCRT
public import ArtinMatthews.GiantMarkedCharacterCriterion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual centered Section 6 coefficient test splits into the literal
giant-prime count and its original reciprocal-mass baseline. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def giantCubicSamplingCenteredSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ) (r : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
    H u * giantMarkedCenteredCore ε x u * giantCubicSamplingKernel η χ Φ x r u

theorem giantCubicSamplingCenteredSum_eq (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ)
    {ε x : ℝ} (hx : 4 ≤ x) (hε : ε ≤ 1 / 4) (r : ℕ) :
    giantCubicSamplingCenteredSum η χ H Φ ε x r =
      giantCubicSamplingGiantSum η χ H Φ ε x r -
        (giantPrimeReciprocalSum x ε : ℂ) * giantCubicSamplingBaselineSum η χ H Φ x r := by
  unfold giantCubicSamplingCenteredSum giantCubicSamplingGiantSum giantCubicSamplingBaselineSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hu₁, hu₂⟩ := Finset.mem_Icc.mp hu
  have hux : (u : ℝ) ≤ 2 * x :=
    (Nat.cast_le.mpr hu₂).trans (Nat.floor_le (by positivity))
  rw [giantMarkedCenteredCore, boundedGiantIndicator_eq_card hu₁ hux hx hε]
  push_cast
  ring

end ArtinMatthews
