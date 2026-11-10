module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeWeighted
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
public import ArtinMatthews.MarkedMinorArcRawGhostChoiceCauchy
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy for every literal store/promote choice, retaining the
exact reverse energy whose column is evaluated by the factorial transpose. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeChoiceReverseEnergy
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    markedRawEdgeChoicePrimeMass ν V hZ s c *
      ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ *
      (markedRawMemorySchurWeight v₀ s.2.2 /
        markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c)) *
      ‖f (markedRawEdgeTargetState hZ s c)‖ ^ 2

theorem markedRawEdgeChoiceReverseEnergy_nonneg
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    0 ≤ markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s := by
  unfold markedRawEdgeChoiceReverseEnergy
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c) (norm_nonneg _))
    (div_nonneg (markedRawMemorySchurWeight_pos hv₀ _).le
      (markedRawMemorySchurWeight_pos hv₀ _).le)) (sq_nonneg _)

/-- Pointwise Cauchy for the actual full physical operation.  No row,
column or operator estimate occurs as a premise. -/
theorem markedRawEdgeApply_choice_cauchy
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    ‖markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f s‖ ^ 2 ≤
      markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) *
        markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s := by
  classical
  have hm (c : MarkedRawEdgeChoice hZ s) :
      ‖(markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ =
        markedRawEdgeChoicePrimeMass ν V hZ s c *
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c)]
  have h := markedGhostChoice_finite_cauchy
    (fun c : MarkedRawEdgeChoice hZ s => (markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c)
    (fun c => f (markedRawEdgeTargetState hZ s c))
    (fun c => markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c) /
      markedRawMemorySchurWeight v₀ s.2.2)
    (fun _ => div_pos (markedRawMemorySchurWeight_pos hv₀ _)
      (markedRawMemorySchurWeight_pos hv₀ _))
  simp only [hm] at h
  convert h using 1
  congr 1
  unfold markedRawEdgeCrudeWeightedAbsRow markedRawEdgeChoiceReverseEnergy
  simp only [one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  field_simp [(markedRawMemorySchurWeight_pos hv₀ s.2.2).ne',
    (markedRawMemorySchurWeight_pos hv₀ (markedRawEdgeTargetMemory hZ s c)).ne']

end
end ArtinMatthews
