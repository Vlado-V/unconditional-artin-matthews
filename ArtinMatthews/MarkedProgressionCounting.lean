module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Int.CardIntervalMod
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

/-!
# Exact progression counts for represented marking divisors

A term of the represented-divisor expansion imposes `d ∣ u`, while the
prime predecessor progression imposes `r ∣ u + 1`. These conditions are
incompatible unless `d` and `r` are coprime, and otherwise give one residue
class modulo `d*r`, with a uniform interval-count error at most one.

The first interval-count proof is adapted from the genuine source
`OAI.NumberTheory.Ostmann.Construction.IntegerIntervalDistribution`; it
uses only Mathlib's exact floor formula and has no distribution input.
-/

namespace ArtinMatthews

/-- Sharp natural interval count, uniform in the modulus and the residue. -/
theorem marked_interval_residue_error (lo hi q a : ℕ) (hlo : lo ≤ hi) (hq : 0 < q) :
    |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ((hi : ℝ) - lo) / q| ≤ 1 := by
  let A : ℚ := ((lo : ℚ) - a) / q
  let B : ℚ := ((hi : ℚ) - a) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (by exact_mod_cast hlo : (lo : ℚ) ≤ hi) a) hq'.le
  have hf := Int.floor_mono hAB
  have hcard := Nat.Ioc_filter_modEq_card lo hi hq a
  have hcast : (((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) =
      ((⌊B⌋ : ℤ) : ℚ) - ((⌊A⌋ : ℤ) : ℚ) := by
    rw [max_eq_left (sub_nonneg.mpr hf)] at hcard
    exact_mod_cast hcard
  have hA := Int.floor_le A
  have hA' := Int.lt_floor_add_one A
  have hB := Int.floor_le B
  have hB' := Int.lt_floor_add_one B
  have hrat : |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| ≤ 1 := by
    rw [hcast]
    have hid : ((hi : ℚ) - lo) / q = B - A := by dsimp [A, B]; ring
    rw [hid, abs_le]
    constructor <;> linarith
  have hreal : ((|(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using hreal

/-- Shifted divisibility is the residue `-1 mod r`, including `r=1`. -/
theorem marked_shifted_divisibility_iff {r : ℕ} (hr : 0 < r) (u : ℕ) :
    r ∣ u + 1 ↔ Nat.ModEq r u (r - 1) := by
  have heq : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hz : Nat.ModEq r (r - 1 + 1) 0 := by simp [heq, Nat.ModEq]
  constructor
  · intro h
    exact Nat.ModEq.add_right_cancel' 1 ((Nat.modEq_zero_iff_dvd.mpr h).trans hz.symm)
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp ((h.add_right 1).trans hz)

/-- The two divisibility conditions force coprimality. -/
theorem marked_divisor_coprime {d r u : ℕ} (hd : d ∣ u) (hr : r ∣ u + 1) :
    d.Coprime r :=
  Nat.Coprime.of_dvd hd hr (by simp)

/-- CRT with the represented marking divisor retained explicitly. -/
theorem marked_divisor_crt {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (hcop : d.Coprime r) :
    ∃ a < d * r, ∀ u : ℕ, (d ∣ u ∧ r ∣ u + 1) ↔ Nat.ModEq (d * r) u a := by
  let a := Nat.chineseRemainder hcop 0 (r - 1)
  refine ⟨a.val, Nat.chineseRemainder_lt_mul hcop 0 (r - 1) hd.ne' hr.ne', ?_⟩
  intro u
  constructor
  · rintro ⟨hdu, hru⟩
    exact Nat.chineseRemainder_modEq_unique hcop (Nat.modEq_zero_iff_dvd.mpr hdu)
      ((marked_shifted_divisibility_iff hr u).mp hru)
  · intro hu
    have hu' := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr hu
    exact ⟨Nat.modEq_zero_iff_dvd.mp (hu'.1.trans a.property.1),
      (marked_shifted_divisibility_iff hr u).mpr (hu'.2.trans a.property.2)⟩

/-- The precise sharp count needed for each term of the represented-divisor
expansion. Its error does not depend on either modulus. -/
theorem marked_divisor_interval_error (lo hi d r : ℕ) (hlo : lo ≤ hi)
    (hd : 0 < d) (hr : 0 < r) (hcop : d.Coprime r) :
    |(((Finset.Ioc lo hi).filter fun u => d ∣ u ∧ r ∣ u + 1).card : ℝ) -
      ((hi : ℝ) - lo) / (d * r : ℕ)| ≤ 1 := by
  classical
  obtain ⟨a, _ha, hclass⟩ := marked_divisor_crt hd hr hcop
  simpa only [hclass] using marked_interval_residue_error lo hi (d * r) a hlo (Nat.mul_pos hd hr)

/-- Noncoprime marking and progression moduli give no surviving integer. -/
theorem marked_divisor_interval_empty (lo hi d r : ℕ) (hcop : ¬ d.Coprime r) :
    (Finset.Ioc lo hi).filter (fun u => d ∣ u ∧ r ∣ u + 1) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro u _hu h
  exact hcop (marked_divisor_coprime h.1 h.2)

/-- A single formula also records the vanishing local factor in the
noncoprime case. -/
theorem marked_divisor_interval_error_all (lo hi d r : ℕ) (hlo : lo ≤ hi)
    (hd : 0 < d) (hr : 0 < r) :
    |(((Finset.Ioc lo hi).filter fun u => d ∣ u ∧ r ∣ u + 1).card : ℝ) -
      (if d.Coprime r then ((hi : ℝ) - lo) / (d * r : ℕ) else 0)| ≤ 1 := by
  by_cases hcop : d.Coprime r
  · rw [ite_eq_left hcop]
    exact marked_divisor_interval_error lo hi d r hlo hd hr hcop
  · rw [ite_eq_right hcop, marked_divisor_interval_empty lo hi d r hcop]
    norm_num

end ArtinMatthews
