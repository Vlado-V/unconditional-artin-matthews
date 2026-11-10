module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! A finite weighted counting inequality for literal choice costs.
Its later orphan specialization keeps the actual source memory cutoff;
no change to a full-band memory bound is involved. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] {C : I → Type*} [∀ i,Fintype (C i)]

def markedMemoryChoiceCount (cost : (i : I) → C i → ℕ) (c : (i : I) → C i) : ℕ :=
  ∑ i,cost i (c i)

theorem markedMemoryChoiceCount_generating
    (cost : (i : I) → C i → ℕ) (w : (i : I) → C i → ℝ) (r : ℝ) :
    (∑ c : (i : I) → C i,r ^ markedMemoryChoiceCount cost c * ∏ i,w i (c i)) =
      ∏ i,∑ a : C i,r ^ cost i a * w i a := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl

theorem markedMemoryChoiceCount_tail_mul
    (cost : (i : I) → C i → ℕ) (w : (i : I) → C i → ℝ)
    (hw : ∀ i a,0≤w i a) (r : ℝ) (hr : 1≤r) (m : ℕ) :
    r^m * (∑ c : (i : I) → C i,
      if m ≤ markedMemoryChoiceCount cost c then ∏ i,w i (c i) else 0) ≤
      ∏ i,∑ a : C i,r ^ cost i a * w i a := by
  rw [← markedMemoryChoiceCount_generating cost w r,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hp : 0≤∏ i,w i (c i) := Finset.prod_nonneg (fun i _ => hw i (c i))
  by_cases hc : m ≤ markedMemoryChoiceCount cost c
  · simp only [hc,ite_true]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr hc) hp
  · simp only [hc,ite_false,mul_zero]
    exact mul_nonneg (pow_nonneg (by linarith) _) hp

theorem markedMemoryChoiceCount_tail
    (cost : (i : I) → C i → ℕ) (w : (i : I) → C i → ℝ)
    (hw : ∀ i a,0≤w i a) (r : ℝ) (hr : 1≤r) (m : ℕ) :
    (∑ c : (i : I) → C i,
      if m ≤ markedMemoryChoiceCount cost c then ∏ i,w i (c i) else 0) ≤
      (∏ i,∑ a : C i,r ^ cost i a * w i a)/r^m := by
  have hp : 0<r^m := pow_pos (by linarith) _
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using markedMemoryChoiceCount_tail_mul cost w hw r hr m

end
end ArtinMatthews
