module

public import ArtinMatthews.Definitions
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

/-- Multiplication by `-3` turns a number in `-3 ℚ×²` into an integer square. -/
theorem negative_three_mul_isSquare {z : ℤ} (hz : NegativeThreeRationalSquare z) :
    IsSquare ((-3 : ℤ) * z) := by
  obtain ⟨q, _, hq⟩ := hz
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨3 * q, ?_⟩
  push_cast
  rw [hq]
  ring

/-- A rational square in this square class has an integral square representative. -/
theorem negativeThreeRationalSquare_int {z : ℤ} (hz : NegativeThreeRationalSquare z) :
    ∃ b : ℤ, z = -3 * b ^ 2 := by
  obtain ⟨b, hb⟩ := negative_three_mul_isSquare hz
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbmod : (b : ZMod 3) * (b : ZMod 3) = 0 := by
    have h := congrArg (fun n : ℤ => (n : ZMod 3)) hb
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      show (3 : ZMod 3) = 0 by decide, neg_zero, zero_mul] using h.symm
  have hbzero : (b : ZMod 3) = 0 := (mul_self_eq_zero.mp hbmod)
  have hbdiv : (3 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hbzero
  obtain ⟨k, hk⟩ := hbdiv
  refine ⟨k, ?_⟩
  rw [hk] at hb
  nlinarith [hb]

/-- In particular the integer in this square class is divisible by three. -/
theorem negativeThreeRationalSquare_three_dvd {z : ℤ} (hz : NegativeThreeRationalSquare z) :
    (3 : ℤ) ∣ z := by
  obtain ⟨b, hb⟩ := negativeThreeRationalSquare_int hz
  refine ⟨-(b ^ 2), ?_⟩
  rw [hb]
  ring

/-- Away from the prime `3`, multiplication by a rational square preserves the
quadratic character of `-3`. -/
theorem negativeThreeRationalSquare_legendre {p : ℕ} [Fact p.Prime] {z : ℤ}
    (hp3 : p ≠ 3) (hz : NegativeThreeRationalSquare z)
    (hz0 : (z : ZMod p) ≠ 0) :
    legendreSym p z = legendreSym p (-3) := by
  have hp : p.Prime := Fact.out
  have hthreeNat : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hp.ne_one)
  have hthree : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    simpa using neg_ne_zero.mpr hthreeNat
  have hs := negative_three_mul_isSquare hz
  have hsmod : IsSquare (((-3 : ℤ) * z : ℤ) : ZMod p) := by
    obtain ⟨b, hb⟩ := hs
    exact ⟨(b : ZMod p), by simpa only [Int.cast_mul] using congrArg (fun n : ℤ => (n : ZMod p)) hb⟩
  have hprod : legendreSym p (-3) * legendreSym p z = 1 := by
    rw [← legendreSym.mul]
    apply (legendreSym.eq_one_iff p ?_).2 hsmod
    simpa using mul_ne_zero hthree hz0
  rcases legendreSym.eq_one_or_neg_one p hthree with h | h
  · simpa [h] using hprod
  · simp only [h, neg_mul, one_mul] at hprod
    omega

end ArtinMatthews
