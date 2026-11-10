module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring.RingNF


set_option backward.privateInPublic true
@[expose] public section

/-! The exact bulk coefficient in the cubic Jacquet shell sum. -/

namespace ArtinMatthews
open scoped BigOperators

theorem sourceJacquet_geometric_bulk {K : Type*} [Field K] (Q : K) (hQ : Q ≠ 0) (e : ℕ) :
    1 + (∑ l ∈ Finset.Icc 1 e, if 3 ∣ l then Q ^ (l / 3) * (1 - Q⁻¹) else 0) =
      Q ^ (e / 3) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ih]
    by_cases he : 3 ∣ e + 1
    · rw [ite_eq_left he, show (e + 1) / 3 = e / 3 + 1 by omega, pow_succ]
      have hmul : Q * (1 - Q⁻¹) = Q - 1 := by rw [mul_sub, mul_one, mul_inv_cancel₀ hQ]
      rw [mul_assoc, hmul]
      ring
    · rw [ite_eq_right he, add_zero, show (e + 1) / 3 = e / 3 by omega]

end ArtinMatthews
