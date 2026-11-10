module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
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

namespace OAI

/-! The free residue digits in the mixed congruence count total the
triangular exponent r(r-1)/2. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_congruence_exponent_sum {r k : ℕ} (hrk : r≤k) :
    (∑ j∈range k, (r-min (j+1) r)) = r*(r-1)/2 := by
  have hcut : (∑ j∈range r, (r-min (j+1) r)) =
      ∑ j∈range k, (r-min (j+1) r) := by
    apply sum_subset (range_mono hrk)
    intro j _ hj
    have hh : r≤j := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
    rw [Nat.min_eq_right (by omega),Nat.sub_self]
  rw [← hcut]
  calc
    _ = ∑ j∈range r, (r-1-j) := by
      apply sum_congr rfl
      intro j hj
      have hjr := mem_range.mp hj
      omega
    _ = ∑ j∈range r, j := sum_range_reflect (fun j => j) r
    _ = _ := sum_range_id r

theorem halasz_congruence_digit_product {p r k : ℕ} (hrk : r≤k) :
    (∏ j : Fin k, p^(r-min (j.val+1) r)) = p^(r*(r-1)/2) := by
  rw [prod_pow_eq_pow_sum]
  congr 1
  simpa only [← Fin.sum_univ_eq_sum_range] using halasz_congruence_exponent_sum hrk

end TwoPointCorrelations

end OAI
