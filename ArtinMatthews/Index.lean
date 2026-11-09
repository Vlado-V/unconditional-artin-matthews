module

public import ArtinMatthews.Definitions
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic of multiplicative indices and the final product cutoff in §10. -/

namespace ArtinMatthews

/-- The multiplicative index at a prime, used only with nonzero residue hypotheses. -/
noncomputable def multiplicativeIndex (p : ℕ) (a : ℤ) : ℕ :=
  (p - 1) / orderOf (a : ZMod p)

lemma orderOf_pos_mod {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) : 0 < orderOf (a : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  exact Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one ha) (by omega)

lemma orderOf_mul_index {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    orderOf (a : ZMod p) * multiplicativeIndex p a = p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact Nat.mul_div_cancel' (ZMod.orderOf_dvd_card_sub_one ha)

/-- A factor of the index forces the corresponding shortened exponent to be one. -/
lemma pow_eq_one_of_dvd_index {p q k : ℕ} (hp : p.Prime) (hq : q ≠ 0)
    {a : ℤ} (ha : (a : ZMod p) ≠ 0) (hpk : p - 1 = k * q)
    (hqi : q ∣ multiplicativeIndex p a) : (a : ZMod p) ^ k = 1 := by
  obtain ⟨j, hj⟩ := hqi
  have hmul := orderOf_mul_index hp ha
  rw [hj, hpk] at hmul
  have heq : k = orderOf (a : ZMod p) * j := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq)
    nlinarith [hmul]
  apply orderOf_dvd_iff_pow_eq_one.mp
  exact ⟨j, heq⟩

/-- Integer divisibility corresponding to the modular exponent assertion. -/
lemma dvd_pow_sub_one_of_dvd_index {p q k : ℕ} (hp : p.Prime) (hq : q ≠ 0)
    {a : ℤ} (ha : (a : ZMod p) ≠ 0) (hpk : p - 1 = k * q)
    (hqi : q ∣ multiplicativeIndex p a) : (p : ℤ) ∣ a ^ k - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  exact sub_eq_zero.mpr (pow_eq_one_of_dvd_index hp hq ha hpk hqi)

/-- Product of all possible short-exponent exceptional factors. -/
def exceptionalProduct (S : Finset ℤ) (m : ℕ) : ℕ :=
  ∏ a ∈ S, ∏ j ∈ Finset.Icc 1 m, (a ^ j - 1).natAbs

lemma natAbs_ge_two_of_admissible {S : Finset ℤ} (hS : AdmissibleBases S)
    {a : ℤ} (ha : a ∈ S) : 2 ≤ a.natAbs := by
  obtain ⟨h0, h1, hm1⟩ := hS.2 a ha
  have h := Int.natCast_natAbs a
  rcases le_total 0 a with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg] at h
    omega
  · rw [abs_of_nonpos hnonpos] at h
    omega

lemma pow_sub_one_ne_zero {a : ℤ} (ha : 2 ≤ a.natAbs) {j : ℕ} (hj : 1 ≤ j) :
    a ^ j - 1 ≠ 0 := by
  intro h
  have heq : a ^ j = 1 := sub_eq_zero.mp h
  have habs := congrArg Int.natAbs heq
  rw [Int.natAbs_pow] at habs
  have hgt : 1 < a.natAbs ^ j := one_lt_pow₀ (by omega) (by omega)
  norm_num at habs
  omega

lemma exceptionalProduct_pos {S : Finset ℤ} (hS : AdmissibleBases S) (m : ℕ) :
    0 < exceptionalProduct S m := by
  apply Finset.prod_pos
  intro a ha
  apply Finset.prod_pos
  intro j hj
  exact Int.natAbs_pos.mpr (pow_sub_one_ne_zero
    (natAbs_ge_two_of_admissible hS ha) (Finset.mem_Icc.mp hj).1)

lemma dvd_exceptionalProduct {S : Finset ℤ} {a : ℤ} (ha : a ∈ S)
    {m j p : ℕ} (hj : j ∈ Finset.Icc 1 m) (hpa : (p : ℤ) ∣ a ^ j - 1) :
    p ∣ exceptionalProduct S m := by
  have hpn : p ∣ (a ^ j - 1).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hpa)
  exact hpn.trans ((Finset.dvd_prod_of_mem (fun j => (a ^ j - 1).natAbs) hj).trans
    (Finset.dvd_prod_of_mem (fun a => ∏ j ∈ Finset.Icc 1 m, (a ^ j - 1).natAbs) ha))

/-- The remaining large index-prime obstruction is contained in the explicit
finite divisor set of the paper's product. -/
lemma large_index_exception_mem_primeFactors {S : Finset ℤ} (hS : AdmissibleBases S)
    {p q k m : ℕ} (hp : p.Prime) (hq : q ≠ 0) {a : ℤ} (ha : a ∈ S)
    (hap : (a : ZMod p) ≠ 0) (hpk : p - 1 = k * q)
    (hkm : k ≤ m) (hqi : q ∣ multiplicativeIndex p a) :
    p ∈ (exceptionalProduct S m).primeFactors := by
  have hk : 1 ≤ k := by
    have h := hp.two_le
    by_contra hnot
    have : k = 0 := by omega
    simp [this] at hpk
    omega
  apply Nat.mem_primeFactors.mpr
  exact ⟨hp, dvd_exceptionalProduct ha (Finset.mem_Icc.mpr ⟨hk, hkm⟩)
    (dvd_pow_sub_one_of_dvd_index hp hq hap hpk hqi),
    (exceptionalProduct_pos hS m).ne'⟩

end ArtinMatthews
