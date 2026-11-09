module

public import ArtinMatthews.Index
public import ArtinMatthews.PrimitiveArithmetic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Power residues and multiplicative indices

In the cyclic unit group of a finite field, an element is a `q`th power if and
only if `q` divides its multiplicative index, provided `q` divides the group
order. This supplies both directions of the square and cube exclusions used
in the positive-density argument.
-/

namespace ArtinMatthews

/-- The power-residue criterion in a finite cyclic group. It uses the actual
cyclic-group instance and requires no choice of a discrete logarithm. -/
theorem exists_pow_iff_dvd_card_div_orderOf
    {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    (a : G) (q : ℕ) (hq : q ∣ Nat.card G) :
    (∃ b : G, b ^ q = a) ↔ q ∣ Nat.card G / orderOf a := by
  have hpow : (∃ b : G, b ^ q = a) ↔
      orderOf a ∣ Nat.card G / (Nat.card G).gcd q := by
    change a ∈ (powMonoidHom q : G →* G).range ↔ _
    rw [← Subgroup.zpowers_le, IsCyclic.subgroup_le_iff_card_dvd,
      Nat.card_zpowers, IsCyclic.card_powMonoidHom_range]
  rw [hpow, Nat.gcd_eq_right hq, Nat.dvd_div_iff_mul_dvd hq,
    Nat.dvd_div_iff_mul_dvd (orderOf_dvd_natCard (x := a)), Nat.mul_comm]

/-- Divisibility of the multiplicative index is equivalent to being a power
residue. The result holds for every divisor `q` of `p - 1`, not just primes. -/
theorem dvd_multiplicativeIndex_iff_isPowerMod {p q : ℕ} {a : ℤ}
    (hp : p.Prime) (hqd : q ∣ p - 1) (ha : (a : ZMod p) ≠ 0) :
    q ∣ multiplicativeIndex p a ↔ ∃ b : ZMod p, b ^ q = (a : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let u : (ZMod p)ˣ := Units.mk0 (a : ZMod p) ha
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have horder : orderOf u = orderOf (a : ZMod p) := by
    simpa [u] using (orderOf_units (y := u)).symm
  have hqu : q ∣ Nat.card (ZMod p)ˣ := by rwa [hcard]
  have hindex : (∃ b : (ZMod p)ˣ, b ^ q = u) ↔ q ∣ multiplicativeIndex p a := by
    simpa only [hcard, horder, multiplicativeIndex] using
      (exists_pow_iff_dvd_card_div_orderOf u q hqu)
  have hq0 : q ≠ 0 := by
    intro hq0
    have hp2 := hp.two_le
    subst q
    simp only [zero_dvd_iff] at hqd
    omega
  have hpower : (∃ b : (ZMod p)ˣ, b ^ q = u) ↔
      ∃ b : ZMod p, b ^ q = (a : ZMod p) := by
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨(b : ZMod p), ?_⟩
      simpa [u] using congrArg Units.val hb
    · rintro ⟨b, hb⟩
      have hb0 : b ≠ 0 := by
        intro hz
        apply ha
        rw [hz, zero_pow hq0] at hb
        exact hb.symm
      refine ⟨Units.mk0 b hb0, ?_⟩
      apply Units.ext
      simpa [u] using hb
  exact hindex.symm.trans hpower

/-- Failure to be a `q`th power excludes `q` from the index. -/
theorem not_dvd_multiplicativeIndex_of_not_isPowerMod {p q : ℕ} {a : ℤ}
    (hp : p.Prime) (hqd : q ∣ p - 1) (ha : (a : ZMod p) ≠ 0)
    (hnot : ¬ ∃ b : ZMod p, b ^ q = (a : ZMod p)) :
    ¬ q ∣ multiplicativeIndex p a := by
  exact fun hq => hnot ((dvd_multiplicativeIndex_iff_isPowerMod hp hqd ha).mp hq)

/-- At an odd prime, even index is equivalent to being a square. -/
theorem two_dvd_multiplicativeIndex_iff_isSquare {p : ℕ} {a : ℤ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : (a : ZMod p) ≠ 0) :
    2 ∣ multiplicativeIndex p a ↔ IsSquare (a : ZMod p) := by
  have htwo : 2 ∣ p - 1 := even_iff_two_dvd.mp (hp.even_sub_one hp2)
  rw [dvd_multiplicativeIndex_iff_isPowerMod hp htwo ha, isSquare_iff_exists_sq]
  exact exists_congr (fun _ => eq_comm)

/-- A nonsquare has odd multiplicative index at an odd prime. -/
theorem not_two_dvd_multiplicativeIndex_of_not_isSquare {p : ℕ} {a : ℤ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : (a : ZMod p) ≠ 0)
    (hnot : ¬ IsSquare (a : ZMod p)) :
    ¬ 2 ∣ multiplicativeIndex p a :=
  fun htwo => hnot ((two_dvd_multiplicativeIndex_iff_isSquare hp hp2 ha).mp htwo)

/-- Legendre symbol `-1` excludes `2` from the multiplicative index. -/
theorem not_two_dvd_multiplicativeIndex_of_legendre_eq_neg_one
    {p : ℕ} [Fact p.Prime] {a : ℤ} (hp2 : p ≠ 2)
    (ha : (a : ZMod p) ≠ 0) (hleg : legendreSym p a = -1) :
    ¬ 2 ∣ multiplicativeIndex p a := by
  have hp : p.Prime := Fact.out
  exact not_two_dvd_multiplicativeIndex_of_not_isSquare hp hp2 ha
    ((legendreSym.eq_neg_one_iff p).mp hleg)

/-- At a prime split modulo `3`, divisibility of the index by `3` is equivalent
to the cube-residue condition in the paper. -/
theorem three_dvd_multiplicativeIndex_iff_isCubeMod {p : ℕ} {a : ℤ}
    (hp : p.Prime) (hp3 : p % 3 = 1) (ha : (a : ZMod p) ≠ 0) :
    3 ∣ multiplicativeIndex p a ↔ IsCubeMod p a := by
  have hthree : 3 ∣ p - 1 := by omega
  exact dvd_multiplicativeIndex_iff_isPowerMod hp hthree ha

/-- Absence of a cube residue excludes `3` from the index. -/
theorem not_three_dvd_multiplicativeIndex_of_not_isCubeMod {p : ℕ} {a : ℤ}
    (hp : p.Prime) (hp3 : p % 3 = 1) (ha : (a : ZMod p) ≠ 0)
    (hnot : ¬ IsCubeMod p a) :
    ¬ 3 ∣ multiplicativeIndex p a :=
  fun hthree => hnot ((three_dvd_multiplicativeIndex_iff_isCubeMod hp hp3 ha).mp hthree)

end ArtinMatthews
