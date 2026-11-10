module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Card
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Arithmetic of the marked Type II determinant

The expanded Cauchy square in PD §3.1 contains two represented predecessors
`U - 1 = a h` and `V - 1 = b h`. For coprime positive labels, this is
equivalent to the determinant equation `b U - a V = b - a`. These are exact
finite arithmetic statements; no determinant replacement estimate is asserted.
-/

namespace ArtinMatthews

/-- Two predecessors are represented with the same nonnegative quotient. -/
def MarkedCommonQuotient (a b U V : ℕ) : Prop :=
  ∃ h : ℕ, U = 1 + a * h ∧ V = 1 + b * h

/-- The exact common-quotient equation before casting the determinant to integers. -/
theorem markedCommonQuotient_iff_cross {a b U V : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    MarkedCommonQuotient a b U V ↔ b * (U - 1) = a * (V - 1) := by
  constructor
  · rintro ⟨h, rfl, rfl⟩
    simp only [Nat.add_sub_cancel_left]
    ring
  · intro hcross
    have hdiv : a ∣ U - 1 := hab.dvd_of_dvd_mul_left (by
      rw [hcross]
      exact dvd_mul_right _ _)
    obtain ⟨h, hh⟩ := hdiv
    have hhV : V - 1 = b * h := by
      apply Nat.eq_of_mul_eq_mul_left ha
      calc
        a * (V - 1) = b * (U - 1) := hcross.symm
        _ = a * (b * h) := by rw [hh]; ring
    exact ⟨h, by omega, by omega⟩

/-- Natural predecessor cross-products are exactly the signed integer determinant. -/
theorem marked_cross_iff_determinant {a b U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    b * (U - 1) = a * (V - 1) ↔
      (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a := by
  constructor
  · intro h
    have h' := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hU, Nat.cast_sub hV] at h'
    nlinarith
  · intro h
    have h' : (b : ℤ) * ((U : ℤ) - 1) = (a : ℤ) * ((V : ℤ) - 1) := by
      nlinarith
    have h'' : ((b * (U - 1) : ℕ) : ℤ) = ((a * (V - 1) : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_sub hU, Nat.cast_sub hV, Nat.cast_one] using h'
    exact_mod_cast h''

/-- The determinant equation used in the marked Cauchy square. -/
theorem markedCommonQuotient_iff_determinant {a b U V : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    MarkedCommonQuotient a b U V ↔
      (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a :=
  (markedCommonQuotient_iff_cross ha hab hU hV).trans
    (marked_cross_iff_determinant hU hV)

/-- A positive first label makes the common quotient unique. -/
theorem marked_common_quotient_unique {a U h k : ℕ} (ha : 0 < a)
    (hh : U = 1 + a * h) (hk : U = 1 + a * k) : h = k := by
  apply Nat.eq_of_mul_eq_mul_left ha
  omega

/-- On the Type II support `U > 1`, the quotient in the determinant equation is positive. -/
theorem marked_positive_commonQuotient_iff_determinant {a b U V : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hU : 1 < U) (hV : 1 ≤ V) :
    (∃ h : ℕ, 0 < h ∧ U = 1 + a * h ∧ V = 1 + b * h) ↔
      (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a := by
  constructor
  · rintro ⟨h, _hh, hhU, hhV⟩
    exact (markedCommonQuotient_iff_determinant ha hab hU.le hV).mp
      ⟨h, hhU, hhV⟩
  · intro hdet
    obtain ⟨h, hhU, hhV⟩ :=
      (markedCommonQuotient_iff_determinant ha hab hU.le hV).mpr hdet
    have hh : 0 < h := by
      by_contra! hn
      have : h = 0 := Nat.eq_zero_of_le_zero hn
      simp [this] at hhU
      omega
    exact ⟨h, hh, hhU, hhV⟩

/-- Product endpoint specialization `U = mn`, `V = rs` of PD's determinant equation. -/
theorem marked_product_commonQuotient_iff_determinant {a b m n r s : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hmn : 1 < m * n) (hrs : 1 ≤ r * s) :
    (∃ h : ℕ, 0 < h ∧ m * n = 1 + a * h ∧ r * s = 1 + b * h) ↔
      (b : ℤ) * m * n - (a : ℤ) * r * s = (b : ℤ) - a := by
  simpa only [Nat.cast_mul, mul_assoc] using
    (marked_positive_commonQuotient_iff_determinant ha hab hmn hrs)

/-- The quotient lies below its positive endpoint, hence in any endpoint cutoff. -/
theorem marked_quotient_mem_range {a U h H : ℕ} (ha : 0 < a)
    (hh : U = 1 + a * h) (hU : U ≤ H) : h ∈ Finset.range H := by
  have hprod : h ≤ a * h := by
    simpa using Nat.mul_le_mul_right h (show 1 ≤ a from ha)
  apply Finset.mem_range.mpr
  omega

/-- The common quotient is the actual natural-number quotient of the predecessor. -/
theorem marked_quotient_eq_div {a U h : ℕ} (ha : 0 < a)
    (hh : U = 1 + a * h) : h = (U - 1) / a := by
  have hsub : U - 1 = a * h := by omega
  rw [hsub, Nat.mul_div_cancel_left _ ha]

/-- The sharper support bound used for a dyadic label of size `a`: if the
endpoint is at most `a H`, then its common quotient is strictly below `H`. -/
theorem marked_quotient_mem_range_of_mul_bound {a U h H : ℕ}
    (hh : U = 1 + a * h) (hU : U ≤ a * H) : h ∈ Finset.range H := by
  apply Finset.mem_range.mpr
  by_contra! hle
  have hmul : a * H ≤ a * h := Nat.mul_le_mul_left a hle
  omega

/-- The determinant picks exactly one common quotient, if it picks any. -/
theorem marked_unique_commonQuotient_iff_determinant {a b U V : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∃! h : ℕ, U = 1 + a * h ∧ V = 1 + b * h) ↔
      (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a := by
  constructor
  · rintro ⟨h, hh, _hunique⟩
    exact (markedCommonQuotient_iff_determinant ha hab hU hV).mp ⟨h, hh⟩
  · intro hdet
    obtain ⟨h, hh⟩ := (markedCommonQuotient_iff_determinant ha hab hU hV).mpr hdet
    exact ⟨h, hh, fun k hk => marked_common_quotient_unique ha hk.1 hh.1⟩

/-- Exact finite counting form of the determinant replacement before the major arcs:
the common quotient is uniquely counted below any upper bound for `U`. -/
theorem marked_commonQuotient_count {a b U V H : ℕ}
    (ha : 0 < a) (hab : a.Coprime b)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : U ≤ H) :
    ((Finset.range H).filter (fun h => U = 1 + a * h ∧ V = 1 + b * h)).card =
      if (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a then 1 else 0 := by
  classical
  by_cases hdet : (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a
  · rw [ite_eq_left hdet]
    apply Finset.card_eq_one_iff_existsUnique.mpr
    obtain ⟨h, hh⟩ := (markedCommonQuotient_iff_determinant ha hab hU hV).mpr hdet
    refine ⟨h, Finset.mem_filter.mpr ⟨marked_quotient_mem_range ha hh.1 hH, hh⟩, ?_⟩
    intro k hk
    exact marked_common_quotient_unique ha (Finset.mem_filter.mp hk).2.1 hh.1
  · rw [ite_eq_right hdet, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro h _hh hh
    exact hdet ((markedCommonQuotient_iff_determinant ha hab hU hV).mp ⟨h, hh⟩)

/-- The common-quotient sum removes `h` exactly while retaining an arbitrary
complex endpoint coefficient. -/
theorem marked_commonQuotient_sum {a b U V H : ℕ}
    (ha : 0 < a) (hab : a.Coprime b)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : U ≤ H) (z : ℂ) :
    (∑ h ∈ Finset.range H, if U = 1 + a * h ∧ V = 1 + b * h then z else 0) =
      if (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a then z else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, marked_commonQuotient_count ha hab hU hV hH]
  split_ifs <;> simp

/-- The exact count with the sharp endpoint-to-label bound `U ≤ a H`.
This is the form compatible with the `X / Y` Cauchy support. -/
theorem marked_commonQuotient_count_of_mul_bound {a b U V H : ℕ}
    (ha : 0 < a) (hab : a.Coprime b)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : U ≤ a * H) :
    ((Finset.range H).filter (fun h => U = 1 + a * h ∧ V = 1 + b * h)).card =
      if (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a then 1 else 0 := by
  classical
  by_cases hdet : (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a
  · rw [ite_eq_left hdet]
    apply Finset.card_eq_one_iff_existsUnique.mpr
    obtain ⟨h, hh⟩ := (markedCommonQuotient_iff_determinant ha hab hU hV).mpr hdet
    refine ⟨h, Finset.mem_filter.mpr
      ⟨marked_quotient_mem_range_of_mul_bound hh.1 hH, hh⟩, ?_⟩
    intro k hk
    exact marked_common_quotient_unique ha (Finset.mem_filter.mp hk).2.1 hh.1
  · rw [ite_eq_right hdet, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro h _hh hh
    exact hdet ((markedCommonQuotient_iff_determinant ha hab hU hV).mp ⟨h, hh⟩)

/-- Sharp-cutoff common-quotient elimination, retaining any complex endpoint coefficient. -/
theorem marked_commonQuotient_sum_of_mul_bound {a b U V H : ℕ}
    (ha : 0 < a) (hab : a.Coprime b)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : U ≤ a * H) (z : ℂ) :
    (∑ h ∈ Finset.range H, if U = 1 + a * h ∧ V = 1 + b * h then z else 0) =
      if (b : ℤ) * U - (a : ℤ) * V = (b : ℤ) - a then z else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul,
    marked_commonQuotient_count_of_mul_bound ha hab hU hV hH]
  split_ifs <;> simp

end ArtinMatthews
