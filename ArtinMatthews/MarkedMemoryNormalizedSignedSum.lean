module

public import ArtinMatthews.MarkedMemoryNormalizedBoundedIndex
public import ArtinMatthews.MarkedMemoryNormalizedFiberSum
public import ArtinMatthews.MarkedMemoryActualIdentityBound
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed normalization of the complete finite tableau sum.
Only the particle-label factorial is cancelled. Birth factorials, both
copied-slot normalizations, every guard and the terminal test remain
inside the original chronological coefficient and functional. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ)

local notation "K" => markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)
local notation "W" => markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset
local notation "assemble" => markedMemoryNormalizedBoundedAssembly (n := n) hZ s K

include hempty in
theorem markedMemoryNormalized_signed_functional_sum
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ i : MarkedMemoryNormalizedBoundedIndex (n := n) hZ s K,
      W (assemble i)*F (assemble i)/(markedMemoryLabelFactorial (fun j => (i.1 j:ℕ)) : ℂ)) =
    ∑ H : MarkedMemoryChronologicalHistory hZ n s,W H*F H := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ N : J → Fin (K+1),∑ H : MarkedMemoryChronologicalHistory hZ n s,
        if ∀ j,Fintype.card (MarkedMemoryActualFiber hZ H j)=(N j:ℕ) then W H*F H else 0 := by
      apply Finset.sum_congr rfl
      intro N _
      simpa only [markedMemoryNormalizedBoundedAssembly,Fintype.card_fin] using
        markedMemoryNormalizedFixed_weighted_sum (A := fun j => Fin (N j:ℕ))
          hZ s hempty ν V ψ η d₀ Y Q ρ qStage χ offset F
    _ = ∑ H : MarkedMemoryChronologicalHistory hZ n s,∑ N : J → Fin (K+1),
        if ∀ j,Fintype.card (MarkedMemoryActualFiber hZ H j)=(N j:ℕ) then W H*F H else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro H _
      exact markedMemoryBoundedCounts_indicator_sum K
        (fun j => Fintype.card (MarkedMemoryActualFiber hZ H j))
        (fun j => markedMemoryActualFiber_card_le hZ H j) (W H*F H)

include hempty in
theorem markedMemoryNormalized_signed_guarded_sum
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ i : MarkedMemoryNormalizedBoundedIndex (n := n) hZ s K,
      if keep (assemble i) then
        W (assemble i)*f (markedMemoryChronologicalTarget hZ (assemble i))/
          (markedMemoryLabelFactorial (fun j => (i.1 j:ℕ)) : ℂ)
      else 0) =
    ∑ H : MarkedMemoryChronologicalHistory hZ n s,
      if keep H then W H*f (markedMemoryChronologicalTarget hZ H) else 0 := by
  simpa only [mul_ite,mul_zero,ite_div,zero_div] using
    markedMemoryNormalized_signed_functional_sum hZ s hempty ν V ψ η d₀ Y Q ρ qStage χ offset
      (fun H => if keep H then f (markedMemoryChronologicalTarget hZ H) else 0)

end
end ArtinMatthews
