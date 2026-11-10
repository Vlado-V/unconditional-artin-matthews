module

public import ArtinMatthews.MarkedMinorArcRawEdgeSlotTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgePatternAction
public import ArtinMatthews.MarkedMinorArcRawEdgePatternTranspose
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact two-sided slot symmetrization of the literal restricted edge. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgePatternSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgePatternApply ν δ γ hZ A (markedRawSlotAverage f))

theorem markedRawEdgePatternSymmetrized_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m))))
    (f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hg : ∀ z active, MarkedRawMemorySymmetric (fun m => g (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawEdgePatternSymmetrized ν δ γ hZ A f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgePatternSymmetrized ν γ δ hZ (markedRawEdgePatternReverse A) g s := by
  unfold markedRawEdgePatternSymmetrized
  rw [markedRawSlotAverage_transpose]
  have ht := markedRawEdgePatternApply_transpose ν δ γ hZ A hAl hAr
    (markedRawSlotAverage f) (markedRawSlotAverage g)
    (markedRawSlotAverage_symmetric f hf) (markedRawSlotAverage_symmetric g hg)
  calc
    _ = ∑ s, (markedRawStateMass ν s : ℂ) * markedRawSlotAverage g s *
        markedRawEdgePatternApply ν δ γ hZ A (markedRawSlotAverage f) s := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := ht
    _ = ∑ s, (markedRawStateMass ν s : ℂ) *
        markedRawEdgePatternApply ν γ δ hZ (markedRawEdgePatternReverse A) (markedRawSlotAverage g) s *
        markedRawSlotAverage f s := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := (markedRawSlotAverage_transpose ν
      (markedRawEdgePatternApply ν γ δ hZ (markedRawEdgePatternReverse A) (markedRawSlotAverage g)) f).symm

theorem markedRawSlotAverageReal_integral
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (F : MarkedRawState P M B Z → ℝ) :
    (∑ s, markedRawStateMass ν s * markedRawSlotAverageReal F s) =
      ∑ s, markedRawStateMass ν s * F s := by
  have h := markedRawSlotAverage_weighted_invariant ν (fun _ => 1) F (fun _ _ => rfl)
  simpa only [mul_one] using h.symm

end
end ArtinMatthews
