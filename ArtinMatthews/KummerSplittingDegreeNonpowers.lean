module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Large prime exponents are not powers of a fixed integer

The numerator of a rational power is the corresponding integer power of its
numerator. For a fixed integer other than `0, 1, -1`, that is impossible once
the exponent is at least its absolute value. This gives a concrete threshold
for the binomial irreducibility needed in the splitting-field degree formula.
-/

namespace ArtinMatthews

lemma natAbs_ge_two_of_not_zero_one_neg_one {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1) : 2 ≤ a.natAbs := by
  have h := Int.natCast_natAbs a
  rcases le_total 0 a with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg] at h
    omega
  · rw [abs_of_nonpos hnonpos] at h
    omega

/-- A rational number cannot have a large power equal to a fixed nontrivial integer. -/
theorem rat_pow_ne_int_of_natAbs_le {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {n : ℕ} (han : a.natAbs ≤ n) (b : ℚ) : b ^ n ≠ (a : ℚ) := by
  intro hpow
  have ha : 2 ≤ a.natAbs := natAbs_ge_two_of_not_zero_one_neg_one ha0 ha1 ham1
  have hn : n ≠ 0 := by omega
  have hnum : b.num ^ n = a := by
    simpa only [Rat.num_pow, Rat.num_intCast] using congrArg Rat.num hpow
  have habs : b.num.natAbs ^ n = a.natAbs := by
    simpa only [Int.natAbs_pow] using congrArg Int.natAbs hnum
  have hbase : 1 < b.num.natAbs := by
    by_contra h
    have hsmall : b.num.natAbs = 0 ∨ b.num.natAbs = 1 := by omega
    rcases hsmall with hz | ho
    · simp only [hz, zero_pow hn] at habs
      omega
    · simp only [ho, one_pow] at habs
      omega
  have hlt : n < b.num.natAbs ^ n := Nat.lt_pow_self hbase
  rw [habs] at hlt
  omega

/-- Binomials `X^q-a` are irreducible for every prime `q` beyond an explicit
threshold depending only on the fixed integer `a`. -/
theorem irreducible_X_pow_sub_intCast_of_large_prime {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    Irreducible (Polynomial.X ^ q - Polynomial.C (a : ℚ)) :=
  X_pow_sub_C_irreducible_of_prime hq (rat_pow_ne_int_of_natAbs_le ha0 ha1 ham1 haq)

/-- The nonpower condition holds eventually for all exponents, not only prime exponents. -/
theorem eventually_rat_pow_ne_int {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ b : ℚ, b ^ n ≠ (a : ℚ) := by
  filter_upwards [Filter.eventually_ge_atTop a.natAbs] with n hn
  exact rat_pow_ne_int_of_natAbs_le ha0 ha1 ham1 hn

/-- Eventual prime-binomial irreducibility, with no unproved arithmetic assumptions. -/
theorem eventually_irreducible_X_pow_sub_intCast {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1) :
    ∀ᶠ q : ℕ in Filter.atTop, q.Prime →
      Irreducible (Polynomial.X ^ q - Polynomial.C (a : ℚ)) := by
  filter_upwards [Filter.eventually_ge_atTop a.natAbs] with q hq
  exact fun hp => irreducible_X_pow_sub_intCast_of_large_prime ha0 ha1 ham1 hp hq

end ArtinMatthews
