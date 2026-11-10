module

public import ArtinMatthews.Index
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import ArtinMatthews.LargeFactor
public import ArtinMatthews.PowerResidues
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

/-! The quadratic, cubic, and congruence exclusions in the final sieve. -/

namespace ArtinMatthews

/-- A prime divisor of a multiplicative index forces the rational prime
itself to be one modulo that index prime. -/
theorem index_prime_forces_one_mod {p q : ℕ} {a : ℤ}
    (hp : p.Prime) (hq : q.Prime) (ha : (a : ZMod p) ≠ 0)
    (hqi : q ∣ multiplicativeIndex p a) : p % q = 1 := by
  have hd : q ∣ p - 1 := hqi.trans (multiplicativeIndex_dvd hp ha)
  have hmod : (p - 1) % q = 0 := Nat.mod_eq_zero_of_dvd hd
  have heq : p = (p - 1) + 1 := by have := hp.two_le; omega
  calc
    p % q = ((p - 1) + 1) % q := congrArg (fun n => n % q) heq
    _ = ((p - 1) % q + 1 % q) % q := Nat.add_mod _ _ _
    _ = 1 := by rw [hmod, zero_add, Nat.mod_eq_of_lt hq.one_lt, Nat.mod_eq_of_lt hq.one_lt]

/-- Every prime at most `Y` is removed from each multiplicative index by
exactly the conditions constructed in Section 10.1 and the enlarged CRT class. -/
theorem no_small_index_prime_of_quadratic_cubic {S : Finset ℤ} {p Y : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ha0 : ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hquad : ∀ a ∈ S, @legendreSym p ⟨hp⟩ a = -1)
    (hcubic : p % 3 = 2 ∨ ∀ a ∈ S, ¬ IsCubeMod p a)
    (havoid : ∀ q : ℕ, q.Prime → 3 < q → q ≤ Y → p % q ≠ 1) :
    ∀ a ∈ S, ∀ q : ℕ, q.Prime → q ≤ Y → ¬ q ∣ multiplicativeIndex p a := by
  let : Fact p.Prime := ⟨hp⟩
  intro a ha q hq hqY hqi
  by_cases hq2 : q = 2
  · subst q
    exact not_two_dvd_multiplicativeIndex_of_legendre_eq_neg_one hp2 (ha0 a ha)
      (hquad a ha) hqi
  by_cases hq3 : q = 3
  · subst q
    have hmod := index_prime_forces_one_mod hp hq (ha0 a ha) hqi
    rcases hcubic with hp3 | hnoncube
    · omega
    · exact not_three_dvd_multiplicativeIndex_of_not_isCubeMod hp hmod (ha0 a ha)
        (hnoncube a ha) hqi
  have hqgt : 3 < q := by have := hq.two_le; omega
  exact havoid q hq hqgt hqY (index_prime_forces_one_mod hp hq (ha0 a ha) hqi)

end ArtinMatthews
