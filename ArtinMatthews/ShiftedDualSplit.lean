module

public import ArtinMatthews.ShiftedDualZeroKloosterman
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Exact separation of the zero and nonzero dual frequencies. Absolute
convergence is proved from that of the two actual coefficient sequences. -/

noncomputable section
open OAI.Erdos970.ErdosKloosterman
open scoped BigOperators
namespace ArtinMatthews

def shiftedDualTerm (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (k : ℕ × ℕ) : ℂ :=
  a k.1 * b k.2 *
    ((if Int.ModEq (D : ℤ) ((m3 : ℤ)^2 * k.1) ((m4 : ℤ)^2 * k.2) then 1 else 0) *
      sum ZMod.stdAddChar ((m3 : ZMod q) - (m4 : ZMod q))
        (((m3 : ZMod q) * (m4 : ZMod q))⁻¹ *
          ((m4 : ZMod q) * k.2 - (m3 : ZMod q) * k.1)))

def shiftedDualNonzeroTerm (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (k : ℕ × ℕ) : ℂ :=
  if m4 * k.2 = m3 * k.1 then 0 else shiftedDualTerm q D m3 m4 a b k

theorem shiftedDualTerm_split (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (k : ℕ × ℕ) :
    shiftedDualTerm q D m3 m4 a b k =
      shiftedDualZeroTerm q D m3 m4 a b k + shiftedDualNonzeroTerm q D m3 m4 a b k := by
  by_cases hz : m4 * k.2 = m3 * k.1 <;>
    simp only [shiftedDualZeroTerm, shiftedDualNonzeroTerm, shiftedDualTerm,
      hz, ite_true, ite_false, zero_add, add_zero]

theorem ordinaryKloosterman_norm_le_card (q : ℕ) [NeZero q] (x y : ZMod q) :
    ‖sum ZMod.stdAddChar x y‖ ≤ Fintype.card (ZMod q)ˣ := by
  classical
  unfold sum
  apply le_trans (norm_sum_le _ _)
  simp only [AddChar.norm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  apply le_of_eq
  exact congrArg (fun i : Fintype (ZMod q)ˣ => (@Fintype.card (ZMod q)ˣ i : ℝ))
    (Subsingleton.elim _ _)

theorem shiftedDualTerm_summable (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) :
    Summable (shiftedDualTerm q D m3 m4 a b) := by
  have hp : Summable (fun k : ℕ × ℕ => a k.1 * b k.2) :=
    summable_mul_of_summable_norm ha.norm hb.norm
  apply (hp.norm.mul_right (Fintype.card (ZMod q)ˣ : ℝ)).of_norm_bounded
  intro k
  unfold shiftedDualTerm
  split_ifs with h
  · simp only [one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ordinaryKloosterman_norm_le_card q _ _) (by positivity)
  · simp only [zero_mul, mul_zero, norm_zero]
    positivity

theorem shiftedDualZeroTerm_summable_of_summable (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) :
    Summable (shiftedDualZeroTerm q D m3 m4 a b) := by
  have h := shiftedDualTerm_summable q D m3 m4 a b ha hb
  apply h.norm.of_norm_bounded
  intro k
  by_cases hz : m4 * k.2 = m3 * k.1
  · simp only [shiftedDualZeroTerm, ite_eq_left hz, shiftedDualTerm, le_refl]
  · simp only [shiftedDualZeroTerm, ite_eq_right hz, norm_zero, norm_nonneg]

theorem shiftedDualNonzeroTerm_summable (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) :
    Summable (shiftedDualNonzeroTerm q D m3 m4 a b) := by
  have h := shiftedDualTerm_summable q D m3 m4 a b ha hb
  apply h.norm.of_norm_bounded
  intro k
  by_cases hz : m4 * k.2 = m3 * k.1
  · simp only [shiftedDualNonzeroTerm, ite_eq_left hz, norm_zero, norm_nonneg]
  · simp only [shiftedDualNonzeroTerm, ite_eq_right hz, le_refl]

theorem shiftedDualSum_split (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) :
    (∑' k, shiftedDualTerm q D m3 m4 a b k) =
      (∑' k, shiftedDualZeroTerm q D m3 m4 a b k) +
        (∑' k, shiftedDualNonzeroTerm q D m3 m4 a b k) := by
  simp_rw [shiftedDualTerm_split q D m3 m4 a b]
  exact (shiftedDualZeroTerm_summable_of_summable q D m3 m4 a b ha hb).tsum_add
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)

end ArtinMatthews
