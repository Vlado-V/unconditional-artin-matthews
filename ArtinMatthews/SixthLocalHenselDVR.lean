module

public import ArtinMatthews.HenselPowerUnits
public import Mathlib.RingTheory.DiscreteValuationRing.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit sixth-power Hensel depth in a discrete valuation ring.
The depth is computed from the actual additive valuation of `6`; no
power-surjectivity or local-norm hypothesis occurs. -/

noncomputable section

namespace ArtinMatthews

open IsLocalRing IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A nonzero principal ideal has exactly its additive-valuation exponent. -/
theorem dvr_span_eq_maximalIdeal_pow (x : R) (hx : x ≠ 0) :
    Ideal.span {x} = IsLocalRing.maximalIdeal R ^ (addVal R x).toNat := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨e, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  rw [hu, addVal_def' u hπ e, ENat.toNat_natCast,
    Ideal.span_singleton_mul_left_unit u.isUnit, hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow]

/-- The strong Hensel depth for sixth roots, including ramified primes over `6`. -/
def sixthHenselDepth (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : ℕ :=
  2 * (addVal R (6 : R)).toNat + 1

theorem sixthHenselDepth_pos : 0 < sixthHenselDepth R := by
  unfold sixthHenselDepth
  omega

/-- The depth ideal is exactly `6²` times the maximal ideal. -/
theorem sixthHenselDepth_ideal (h6 : (6 : R) ≠ 0) :
    IsLocalRing.maximalIdeal R ^ sixthHenselDepth R =
      Ideal.span {(6 : R)^2} * IsLocalRing.maximalIdeal R := by
  rw [sixthHenselDepth, pow_add, pow_one,
    Nat.mul_comm 2, pow_mul, ← dvr_span_eq_maximalIdeal_pow (6 : R) h6,
    Ideal.span_singleton_pow]

theorem sixthHenselDepth_eq_one_of_isUnit (h6 : IsUnit (6 : R)) :
    sixthHenselDepth R = 1 := by
  rw [sixthHenselDepth, addVal_eq_zero_iff.mpr h6]
  rfl

variable [HenselianLocalRing R]

/-- Genuine Hensel lifting at the explicit valuation depth. -/
theorem exists_sixthRoot_of_depth (h6 : (6 : R) ≠ 0) (u : Rˣ)
    (hu : (u : R) - 1 ∈ IsLocalRing.maximalIdeal R ^ sixthHenselDepth R) :
    ∃ w : Rˣ, w^6 = u := by
  apply HenselPower.exists_unit_pow_of_sub_one_mem 6 (by decide) u
  rwa [sixthHenselDepth_ideal h6] at hu

/-- At residue characteristic prime to `6`, every principal unit has a sixth root. -/
theorem exists_sixthRoot_of_principal (h6 : IsUnit (6 : R)) (u : Rˣ)
    (hu : (u : R) - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ w : Rˣ, w^6 = u := by
  apply HenselPower.exists_unit_pow_of_sub_one_mem 6 (by decide) u
  change (u : R) - 1 ∈ Ideal.span {(6 : R)^2} * IsLocalRing.maximalIdeal R
  rw [Ideal.span_singleton_eq_top.mpr (h6.pow 2), Ideal.top_mul]
  exact hu

end ArtinMatthews
