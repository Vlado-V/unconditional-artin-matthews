module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

/-! The actual selected-slot carrier inherits the logarithmic group
count without replacing any ordered labels by numeric products. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators

theorem idealGroupedSlot_card_le {A : Type*} [Fintype A] (k : A → ℕ)
    (m : ℕ) (hk : ∀ i, k i ≤ m) :
    Fintype.card (Σ i, Fin (k i)) ≤ m*Fintype.card A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _i : A, m := sum_le_sum fun i _ => hk i
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]

theorem idealGroupedSlot_card_source {A : Type*} [Fintype A] (k : A → ℕ)
    (m : ℕ) (hk : ∀ i, k i ≤ m) {C L : ℝ}
    (hcard : (Fintype.card A : ℝ) ≤ C*Real.log L) :
    (Fintype.card (Σ i, Fin (k i)) : ℝ) ≤ ((m : ℝ)*C)*Real.log L := by
  have h := idealGroupedSlot_card_le k m hk
  calc
    _ ≤ (m : ℝ)*(Fintype.card A : ℝ) := by exact_mod_cast h
    _ ≤ (m : ℝ)*(C*Real.log L) := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    _ = _ := by ring

end ArtinMatthews
