module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import ArtinMatthews.ReciprocalTail
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Summing a uniform splitting bound over the small-index primes. -/

namespace ArtinMatthews

/-- The reciprocal kernel in (10.3) sums to at most `1/Y`.
The pointwise splitting estimates are explicit hypotheses. -/
theorem sum_splitting_bounds {P : Finset ℕ} {Y : ℕ} (hY : 0 < Y)
    (hP : ∀ q ∈ P, Y < q) {N : ℕ → ℝ} {X E : ℝ} (hX : 0 ≤ X)
    (hN : ∀ q ∈ P, N q ≤ X / ((q : ℝ) * ((q : ℝ) - 1)) + E) :
    (∑ q ∈ P, N q) ≤ X / Y + (P.card : ℝ) * E := by
  calc
    (∑ q ∈ P, N q) ≤ ∑ q ∈ P, (X / ((q : ℝ) * ((q : ℝ) - 1)) + E) :=
      Finset.sum_le_sum hN
    _ = X * (∑ q ∈ P, 1 / ((q : ℝ) * ((q : ℝ) - 1))) + (P.card : ℝ) * E := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ X * (1 / (Y : ℝ)) + (P.card : ℝ) * E :=
      add_le_add (mul_le_mul_of_nonneg_left (sum_reciprocal_tail_le P Y hY hP) hX) le_rfl
    _ = _ := by ring

/-- Union bound with the uniform splitting main term summed explicitly.
This is the finite step in (10.5), not an assumption-free splitting estimate. -/
theorem card_union_splitting_bounds {α : Type*} [DecidableEq α]
    {P : Finset ℕ} {Y : ℕ} (hY : 0 < Y) (hP : ∀ q ∈ P, Y < q)
    (F : ℕ → Finset α) {X E : ℝ} (hX : 0 ≤ X)
    (hF : ∀ q ∈ P, ((F q).card : ℝ) ≤ X / ((q : ℝ) * ((q : ℝ) - 1)) + E) :
    ((P.biUnion F).card : ℝ) ≤ X / Y + (P.card : ℝ) * E := by
  have hcard : ((P.biUnion F).card : ℝ) ≤ ∑ q ∈ P, ((F q).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  exact hcard.trans (sum_splitting_bounds hY hP hX hF)

end ArtinMatthews
