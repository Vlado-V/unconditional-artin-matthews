module

public import ArtinMatthews.HenselPowerPolynomial
public import Mathlib.RingTheory.Henselian


set_option backward.privateInPublic true
@[expose] public section

/-! Strong Hensel lifting for power units using only the genuine Henselian
local-ring axiom. No completeness or characteristic-zero hypothesis is
needed after the Henselian local ring instance has been supplied. -/
noncomputable section
namespace ArtinMatthews.HenselPower
open Polynomial IsLocalRing
open scoped BigOperators
variable {R : Type*} [CommRing R]

theorem powerPolynomial_map_of_eq_zero {S : Type*} [CommRing S]
    (φ : R →+* S) (d : ℕ) {t : R} (ht : φ t = 0) :
    (powerPolynomial d t).map φ = X^d - X^(d-1) := by
  simp only [powerPolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, powerTail, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, map_mul, map_natCast, map_pow, ht,
    zero_pow (Nat.succ_ne_zero _), mul_zero, C_0, zero_mul, Finset.sum_const_zero, add_zero]

variable [HenselianLocalRing R]

/-- The monic auxiliary polynomial has a unit root congruent to one. -/
theorem exists_unit_root_powerPolynomial (d : ℕ) (hd : 0 < d)
    {t : R} (ht : t ∈ maximalIdeal R) :
    ∃ w : Rˣ, (powerPolynomial d t).IsRoot (w : R) := by
  have ht0 : residue R t = 0 := (residue_eq_zero_iff t).mpr ht
  have hmap := powerPolynomial_map_of_eq_zero (residue R) d ht0
  have heval : (powerPolynomial d t).eval 1 ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    have h := congrArg (fun f : (ResidueField R)[X] => f.eval 1) hmap
    simpa only [eval_map, eval₂_at_one, eval_sub, eval_pow, eval_X,
      map_one, one_pow, sub_self] using h
  have hder : IsUnit ((powerPolynomial d t).derivative.eval 1) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have h := congrArg (fun f : (ResidueField R)[X] => f.derivative.eval 1) hmap
    have hone : residue R ((powerPolynomial d t).derivative.eval 1) = 1 := by
      simpa only [derivative_map, eval_map, eval₂_at_one, derivative_sub,
        derivative_X_pow, eval_sub, eval_mul, eval_C, eval_pow, eval_X, map_one, one_pow,
        mul_one, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, sub_sub_cancel] using h
    rw [hone]
    exact one_ne_zero
  obtain ⟨w, hw, hw1⟩ := HenselianLocalRing.is_henselian
    (powerPolynomial d t) (powerPolynomial_monic d hd t) 1 heval hder
  have hwres : residue R w = 1 := by
    have h := (residue_eq_zero_iff _).mpr hw1
    simpa only [map_sub, map_one, sub_eq_zero] using h
  have hwu : IsUnit w := (residue_ne_zero_iff_isUnit w).mp (hwres ▸ one_ne_zero)
  exact ⟨hwu.unit, by simpa only [IsUnit.unit_spec] using hw⟩

/-- Every unit congruent to one modulo d² times the maximal ideal is a d-th
power. This is the local power statement needed for a quantitative norm modulus. -/
theorem exists_unit_pow_of_eq_one_add (d : ℕ) (hd : 0 < d) (u : Rˣ)
    {t : R} (ht : t ∈ maximalIdeal R) (hu : (u : R) = 1 + (d : R)^2 * t) :
    ∃ v : Rˣ, v^d = u := by
  obtain ⟨w, hw⟩ := exists_unit_root_powerPolynomial d hd ht
  let v : R := ((w : R) + (d : R) * t) * (↑(w⁻¹) : R)
  have hvpow : v^d = (u : R) := by
    rw [show v = ((w : R) + (d : R) * t) * (↑(w⁻¹) : R) from rfl, mul_pow,
      power_eq_of_isRoot d hd t w hw, ← hu]
    rw [mul_assoc, ← mul_pow]
    simp
  have hv : IsUnit v := (isUnit_pow_iff hd.ne').mp (hvpow ▸ u.isUnit)
  refine ⟨hv.unit, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hvpow

/-- Ideal-membership form of strong Hensel power lifting. -/
theorem exists_unit_pow_of_sub_one_mem (d : ℕ) (hd : 0 < d) (u : Rˣ)
    (hu : (u : R) - 1 ∈ Ideal.span {(d : R)^2} * maximalIdeal R) :
    ∃ v : Rˣ, v^d = u := by
  obtain ⟨t, ht, htu⟩ := Ideal.mem_span_singleton_mul.mp hu
  apply exists_unit_pow_of_eq_one_add d hd u ht
  rw [htu]
  ring

end ArtinMatthews.HenselPower
