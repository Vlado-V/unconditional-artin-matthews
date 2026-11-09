module

public import ArtinMatthews.Definitions


set_option backward.privateInPublic true
@[expose] public section

/-!
# Elementary restrictions on primitive roots

A generator of the multiplicative group modulo a prime cannot be a proper
power whose exponent divides the group order. The quadratic and cubic cases
give the arithmetic restrictions used in the two finite obstructions.
-/

namespace ArtinMatthews

/-- A primitive root is not a q-th power when q > 1 divides p - 1. -/
theorem primitive_not_power_of_dvd {p q : ℕ} {a : ℤ}
    (hp : p.Prime) (hq : 1 < q) (hqd : q ∣ p - 1)
    (h : IsPrimitiveRootMod p a) :
    ¬ ∃ b : ZMod p, b ^ q = (a : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨b, hb⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    apply h.1
    rw [← hb, hb0, zero_pow (by omega)]
  have hn : 0 < p - 1 := by have := hp.two_le; omega
  have hk : 0 < (p - 1) / q :=
    Nat.div_pos (Nat.le_of_dvd hn hqd) (by omega)
  have hpow : (a : ZMod p) ^ ((p - 1) / q) = 1 := by
    rw [← hb, ← pow_mul, Nat.mul_div_cancel' hqd]
    exact ZMod.pow_card_sub_one_eq_one hb0
  have hle := orderOf_le_of_pow_eq_one hk hpow
  rw [h.2] at hle
  exact (not_le_of_gt (Nat.div_lt_self hn hq)) hle

/-- Every primitive root at an odd prime has Legendre symbol -1. -/
theorem primitive_legendre_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ}
    (hp2 : p ≠ 2) (h : IsPrimitiveRootMod p a) :
    legendreSym p a = -1 := by
  apply (legendreSym.eq_neg_one_iff_not_one p h.1).mpr
  intro ha
  have hsq := (legendreSym.eq_one_iff p h.1).mp ha
  have hpow := (ZMod.euler_criterion p h.1).mp hsq
  have hp : p.Prime := Fact.out
  have hpos : 0 < p / 2 := Nat.div_pos hp.two_le (by norm_num)
  have hle := orderOf_le_of_pow_eq_one hpos hpow
  rw [h.2] at hle
  have := hp.two_le
  omega

/-- At a prime congruent to 1 modulo 3 a primitive root is not a cube. -/
theorem primitive_not_cube {p : ℕ} {a : ℤ}
    (hp : p.Prime) (hp3 : p % 3 = 1) (h : IsPrimitiveRootMod p a) :
    ¬ IsCubeMod p a := by
  apply primitive_not_power_of_dvd hp (by norm_num : 1 < 3) _ h
  omega

end ArtinMatthews
