module

public import ArtinMatthews.Definitions
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Extending character agreement from prime factors

Two multiplicative functions on the integers agree on an integer once they
agree on minus one and on every prime divisor of its absolute value.  This is
the factorization step in the global quadratic progression argument.
-/

namespace ArtinMatthews

section MonoidWithZero

variable {M : Type*} [MonoidWithZero M]

/-- Agreement on the prime divisors of a natural number extends to the
number for homomorphisms defined on the integers. -/
theorem int_hom_eq_on_nat_of_prime_divisors (f g : ℤ →*₀ M) (n : ℕ)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ n → f (q : ℤ) = g (q : ℤ)) :
    f (n : ℤ) = g (n : ℤ) := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact hprime p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul, map_mul, map_mul]
    congr 1
    · exact ha (fun q hq hqa => hprime q hq (hqa.trans (dvd_mul_right a b)))
    · exact hb (fun q hq hqb => hprime q hq (hqb.trans (dvd_mul_left b a)))

/-- Agreement on minus one and all prime divisors of the absolute value
extends to the integer itself.  The zero case is included automatically. -/
theorem int_hom_eq_of_prime_divisors (f g : ℤ →*₀ M) (a : ℤ)
    (hneg : f (-1) = g (-1))
    (hprime : ∀ q : ℕ, q.Prime → q ∣ a.natAbs → f (q : ℤ) = g (q : ℤ)) :
    f a = g a := by
  cases a with
  | ofNat n =>
    exact int_hom_eq_on_nat_of_prime_divisors f g n (by simpa using hprime)
  | negSucc n =>
    have hn : f ((n + 1 : ℕ) : ℤ) = g ((n + 1 : ℕ) : ℤ) :=
      int_hom_eq_on_nat_of_prime_divisors f g (n + 1) (by simpa using hprime)
    have hre : Int.negSucc n = (-1 : ℤ) * ((n + 1 : ℕ) : ℤ) := by omega
    rw [hre, map_mul, map_mul, hneg, hn]

end MonoidWithZero

end ArtinMatthews
