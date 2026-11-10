module

public import ArtinMatthews.MarkedMemoryHistoryPhaseFactor
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

/-! An actual endpoint cutoff supported in a finite position window
kills every edge leaving it, including each geometric reverse branch.
Both endpoint permutations remain present. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedRawEdgeChoiceCoefficient_eq_zero_of_target_cutoff
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s)
    (hc : χ (markedRawEdgeTargetState hZ s c)=0) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c=0 := by
  have hfactor : markedRawEndpointFactor hZ 1 χ (markedRawEdgeTargetState hZ s c)=0 := by
    simp only [markedRawEndpointFactor,hc,mul_zero,ite_self]
  unfold markedRawEdgeChoiceCoefficient
  simp only [hfactor,mul_zero,ite_self]

theorem markedMemoryEdgeChoiceWeight_eq_zero_of_outside
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (W : Finset (ℤ × ℤ))
    (hχ : ∀ s,s.1.1∉W → χ s=0)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s)
    (hc : c.2.1.target.1∉W) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c=0 := by
  have hz := markedRawEdgeChoiceCoefficient_eq_zero_of_target_cutoff hZ ψ η d₀ Y Q ρ χ
    (markedRawSlotEquiv c.1 s) c.2.1 (hχ _ hc)
  simp only [markedMemoryEdgeChoiceWeight,hz,mul_zero,zero_mul]

theorem markedMemoryGeometricEdgeChoiceWeight_eq_zero_of_outside
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (W : Finset (ℤ × ℤ)) (hχ : ∀ j s,s.1.1∉W → χ j s=0)
    (j : ℕ) (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s)
    (hc : c.2.1.target.1∉W) :
    markedMemoryGeometricEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ orientation χ j s c=0 := by
  unfold markedMemoryGeometricEdgeChoiceWeight
  split_ifs
  · apply markedMemoryEdgeChoiceWeight_eq_zero_of_outside hZ ν V _ _ d₀ Y Q ρ _ W _ s c hc
    intro t ht
    rw [hχ j t ht,star_zero]
  · exact markedMemoryEdgeChoiceWeight_eq_zero_of_outside hZ ν V ψ η d₀ Y Q ρ (χ j) W (hχ j) s c hc

end ArtinMatthews
