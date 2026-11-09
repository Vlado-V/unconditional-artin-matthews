module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Frobenius


set_option backward.privateInPublic true
@[expose] public section

/-!
# Actual integral Frobenius lifts above rational primes

For a finite Galois number field, every rational prime has a maximal ideal
above it and an arithmetic Frobenius lift acting on the ring of integers.
This is an existence statement at every prime; unramifiedness is only needed
for uniqueness, not for the lift or the residue-power identity below.
-/

open NumberField

namespace ArtinMatthews

/-- Concrete prime and Frobenius data above the rational prime `p`. -/
structure IntegralFrobeniusData (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (p : ℕ) where
  primeIdeal : Ideal (𝓞 K)
  maximal : primeIdeal.IsMaximal
  under_eq : primeIdeal.under ℤ = Ideal.span {(p : ℤ)}
  frobenius : Gal(K/ℚ)
  frobenius_spec : IsArithFrobAt ℤ frobenius primeIdeal

/-- The lift is constructed from lying-over and the invariant-ring Frobenius
existence theorem; it is not supplied as a hypothesis. -/
theorem exists_integralFrobeniusData (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} (hp : p.Prime) : Nonempty (IntegralFrobeniusData K p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have : Q.IsMaximal := hQ
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover
  have hQunder : Q.under ℤ = Ideal.span {(p : ℤ)} := hQover.over.symm
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) Q
  exact ⟨⟨Q, hQ, hQunder, σ, hσ⟩⟩

namespace IntegralFrobeniusData

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  {p : ℕ} (D : IntegralFrobeniusData K p)

/-- The chosen maximal ideal has finite residue field. -/
theorem finite_residue : Finite (𝓞 K ⧸ D.primeIdeal) := by
  have : D.primeIdeal.IsMaximal := D.maximal
  infer_instance

/-- The base residue field has exactly `p` elements. -/
theorem base_residue_card : Nat.card (ℤ ⧸ D.primeIdeal.under ℤ) = p := by
  rw [D.under_eq, Int.card_ideal_quot]

/-- The actual residue ring has characteristic `p`. -/
theorem residue_charP : CharP (𝓞 K ⧸ D.primeIdeal) p := by
  apply ringChar.of_eq
  rw [Ideal.ringChar_quot, D.under_eq]
  simp

/-- The Frobenius congruence with exponent the rational prime, without a hidden
residue-degree parameter. -/
theorem frobenius_sub_pow_mem (x : 𝓞 K) :
    D.frobenius • x - x ^ p ∈ D.primeIdeal := by
  simpa only [D.base_residue_card, MulSemiringAction.toAlgHom_apply] using D.frobenius_spec x

/-- The lifted field automorphism induces the actual `p`th-power map on the
finite residue field. -/
theorem residue_frobenius (x : 𝓞 K) :
    Ideal.Quotient.mk D.primeIdeal (D.frobenius • x) =
      (Ideal.Quotient.mk D.primeIdeal x) ^ p := by
  rw [← map_pow, Ideal.Quotient.eq]
  exact D.frobenius_sub_pow_mem x

/-- An integer not divisible by `p` does not vanish at the selected prime. -/
theorem int_not_mem {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    (a : 𝓞 K) ∉ D.primeIdeal := by
  intro h
  have hmem : a ∈ D.primeIdeal.under ℤ := h
  rw [D.under_eq, Ideal.mem_span_singleton] at hmem
  exact ha hmem

/-- Root-of-unity Frobenius action is exact in characteristic zero, not merely
a congruence, whenever the order is prime to the residue characteristic. -/
theorem frobenius_root_of_unity {ζ : 𝓞 K} {m : ℕ}
    (hζ : ζ ^ m = 1) (hm : ¬ (p : ℤ) ∣ (m : ℤ)) :
    D.frobenius • ζ = ζ ^ p := by
  have hmQ : (m : 𝓞 K) ∉ D.primeIdeal := by simpa only [Int.cast_natCast] using D.int_not_mem hm
  simpa only [D.base_residue_card, MulSemiringAction.toAlgHom_apply] using
    D.frobenius_spec.apply_of_pow_eq_one hζ hmQ

end IntegralFrobeniusData

end ArtinMatthews
