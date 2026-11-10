module

public import ArtinMatthews.MarkedMemoryNormalizedEndpointWeight
public import ArtinMatthews.MarkedMemoryNormalizedBoundedIndex
public import ArtinMatthews.MarkedMemoryNormalizedFiberSum
public import ArtinMatthews.MarkedMemoryNormalizedSignedSum
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

/-! The complete signed source sum on the faithful bounded normalized
endpoint family. Label factorials normalize the proven relabel fibers;
birth factorials and both copied-slot factors remain in the actual
coefficient, with the original guard and terminal observable. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "K" => markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)
local notation "assemble" => markedMemoryNormalizedBoundedAssembly (n := n) hZ s K

include hempty in
theorem markedMemoryNormalized_endpoint_guarded_sum
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ i : MarkedMemoryNormalizedBoundedIndex (n := n) hZ s K,
      if keep (assemble i) then
        markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ i.2 *
          f (markedMemoryChronologicalTarget hZ (assemble i)) /
            (markedMemoryLabelFactorial (fun j => (i.1 j:ℕ)) : ℂ)
      else 0) =
    ∑ H : MarkedMemoryChronologicalHistory hZ n s,
      if keep H then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
          (markedMemoryHistoryVisitSchedule q n) χ n 0 H * f (markedMemoryChronologicalTarget hZ H)
      else 0 := by
  calc
    _ = ∑ i : MarkedMemoryNormalizedBoundedIndex (n := n) hZ s K,
        if keep (assemble i) then
          markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
            (markedMemoryHistoryVisitSchedule q n) χ n 0 (assemble i) *
              f (markedMemoryChronologicalTarget hZ (assemble i)) /
                (markedMemoryLabelFactorial (fun j => (i.1 j:ℕ)) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [markedMemoryNormalizedEndpointWeight_eq]
      rfl
    _ = _ := markedMemoryNormalized_signed_guarded_sum hZ s hempty ν V ψ η d₀ Y Q 1
      (markedMemoryHistoryVisitSchedule q n) χ 0 keep f

end
end ArtinMatthews
