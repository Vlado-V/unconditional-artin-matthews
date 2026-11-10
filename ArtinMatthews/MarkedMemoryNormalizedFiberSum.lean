module

public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
public import ArtinMatthews.MarkedMemoryNormalizedMultiplicity
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

/-! Exact signed summation for a fixed finite label family. The proved
fiber multiplicity cancels its label factorial, while unsupported and
wrong-cardinality histories contribute zero. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

def markedMemoryLabelFactorial {J : Type*} [Fintype J] (N : J → ℕ) : ℕ :=
  ∏ j,(N j).factorial

theorem markedMemoryLabelFactorial_pos {J : Type*} [Fintype J] (N : J → ℕ) :
    0 < markedMemoryLabelFactorial N := Finset.prod_pos (fun j _ => Nat.factorial_pos (N j))

theorem markedMemoryLabelFactorial_complex_ne_zero {J : Type*} [Fintype J] (N : J → ℕ) :
    (markedMemoryLabelFactorial N : ℂ)≠0 := by
  exact_mod_cast (Nat.ne_of_gt (markedMemoryLabelFactorial_pos N))

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ)

local notation "W" => markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset
local notation "assemble" => markedMemoryNormalizedHistoryAssembly (A := A) (n := n) hZ s

include hempty in
theorem markedMemoryNormalizedFixed_weighted_sum
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s,
      W (assemble i)*F (assemble i)/(markedMemoryLabelFactorial (fun j => Fintype.card (A j)) : ℂ)) =
    ∑ H : MarkedMemoryChronologicalHistory hZ n s,
      if ∀ j,Fintype.card (MarkedMemoryActualFiber hZ H j)=Fintype.card (A j)
      then W H*F H else 0 := by
  rw [← Fintype.sum_fiberwise' assemble
    (fun H => W H*F H/(markedMemoryLabelFactorial (fun j => Fintype.card (A j)) : ℂ))]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  by_cases hw : W H=0
  · simp only [hw,zero_mul,zero_div,mul_zero,ite_self]
  · have hc := markedMemoryNormalizedFiber_card_eq_if_of_weight_ne_zero
      (A := A) hZ s H hempty ν V ψ η d₀ Y Q ρ qStage χ offset hw
    rw [hc]
    by_cases hm : ∀ j,Fintype.card (MarkedMemoryActualFiber hZ H j)=Fintype.card (A j)
    · rw [ite_eq_left hm,ite_eq_left hm]
      change (markedMemoryLabelFactorial (fun j => Fintype.card (A j)) : ℂ)*
        (W H*F H/(markedMemoryLabelFactorial (fun j => Fintype.card (A j)) : ℂ))=W H*F H
      field_simp [markedMemoryLabelFactorial_complex_ne_zero (fun j => Fintype.card (A j))]
    · rw [ite_eq_right hm,ite_eq_right hm]
      simp only [Nat.cast_zero,zero_mul]

end
end ArtinMatthews
