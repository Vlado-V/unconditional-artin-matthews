module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Frobenius
public import ArtinMatthews.ArtinAbelianFrobeniusOrder
public import ArtinMatthews.ArtinAbelianLocalCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! Actual local Artin factorization for finite abelian extensions of number
fields. At ramified primes the characters are precisely characters of the
actual inertia quotient; no Euler factors are deleted. -/

noncomputable section
namespace ArtinMatthews.AbelianLocal
open scoped NumberField IsMulCommutative Classical BigOperators

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

/-- The quotient of the inertia quotient by its actual Frobenius cyclic
subgroup has cardinal equal to the genuine prime-ideal fiber. -/
theorem card_inertiaQuotient_frobenius_quotient
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (σ : Gal(E/F)) (H : IsArithFrobAt (𝓞 F) σ Q) :
    Nat.card ((Gal(E/F) ⧸ Q.inertia Gal(E/F)) ⧸
      Subgroup.zpowers (QuotientGroup.mk σ : Gal(E/F) ⧸ Q.inertia Gal(E/F))) =
      Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) := by
  let I := Q.inertia Gal(E/F)
  let g : Gal(E/F) ⧸ I := QuotientGroup.mk σ
  have ho : orderOf g = Q.inertiaDeg (𝓞 F) :=
    orderOf_frobenius_mod_inertia F E P.asIdeal Q σ H
  have hcount := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(E/F)) P.asIdeal Q
  have hgroup : Nat.card ((Gal(E/F) ⧸ I) ⧸ Subgroup.zpowers g) *
      (Nat.card I * orderOf g) = Nat.card Gal(E/F) := by
    calc
      _ = (Nat.card ((Gal(E/F) ⧸ I) ⧸ Subgroup.zpowers g) * orderOf g) * Nat.card I := by ring
      _ = Nat.card (Gal(E/F) ⧸ I) * Nat.card I := by
        rw [← Nat.card_zpowers g, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      _ = Nat.card Gal(E/F) := (Subgroup.card_eq_card_quotient_mul_card_subgroup I).symm
  have hcount' : Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) *
      (Nat.card I * orderOf g) = Nat.card Gal(E/F) := by
    simpa only [I, ho, mul_assoc, Nat.card_coe_set_eq] using hcount
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos (orderOf_pos g))
    (hgroup.trans hcount'.symm)

local instance inertiaCharacterFintype (Q : Ideal (𝓞 E)) :
    Fintype ((Gal(E/F) ⧸ Q.inertia Gal(E/F)) →* ℂˣ) := Fintype.ofFinite _
local instance primesOverFintype (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Fintype (Ideal.primesOver P.asIdeal (𝓞 E)) := Fintype.ofFinite _

/-- The actual all-prime abelian local Artin factorization. This includes
ramified primes through the actual inertia quotient, without a hypothesis
of unramifiedness or any assumed factorization of zeta functions. -/
theorem abelian_artin_localEuler
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (σ : Gal(E/F)) (H : IsArithFrobAt (𝓞 F) σ Q) (s : ℂ) :
    (∏ χ : (Gal(E/F) ⧸ Q.inertia Gal(E/F)) →* ℂˣ,
      (1 - (χ (QuotientGroup.mk σ) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹) =
      ∏ Q' : Ideal.primesOver P.asIdeal (𝓞 E),
        (1 - (Ideal.absNorm Q'.val : ℂ) ^ (-s))⁻¹ := by
  have ho := orderOf_frobenius_mod_inertia F E P.asIdeal Q σ H
  have hc := card_inertiaQuotient_frobenius_quotient F E P Q σ H
  have hnorm (Q' : Ideal.primesOver P.asIdeal (𝓞 E)) :
      Ideal.absNorm Q'.val = Ideal.absNorm P.asIdeal ^ Q.inertiaDeg (𝓞 F) := by
    let : Q'.val.IsPrime := Q'.property.1
    let : Q'.val.LiesOver P.asIdeal := Q'.property.2
    let : Q'.val.IsMaximal := Q'.property.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver P.ne_bot Q'.property)
    rw [← Ideal.absNorm_pow_inertiaDeg P.asIdeal Q'.val,
      ← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q Q'.val Gal(E/F)]
  have hfactor (Q' : Ideal.primesOver P.asIdeal (𝓞 E)) :
      (Ideal.absNorm Q'.val : ℂ) ^ (-s) =
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ Q.inertiaDeg (𝓞 F) := by
    rw [hnorm Q', Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rw [prod_inertiaQuotient_euler_factors, ho, hc]
  simp_rw [hfactor]
  rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- The all-prime formula for Mathlib's actual chosen arithmetic Frobenius. -/
theorem abelian_artin_localEuler_arithFrobAt
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] (s : ℂ) :
    (∏ χ : (Gal(E/F) ⧸ Q.inertia Gal(E/F)) →* ℂˣ,
      (1 - (χ (QuotientGroup.mk (arithFrobAt (𝓞 F) Gal(E/F) Q)) : ℂ) *
        (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹) =
      ∏ Q' : Ideal.primesOver P.asIdeal (𝓞 E),
        (1 - (Ideal.absNorm Q'.val : ℂ) ^ (-s))⁻¹ :=
  abelian_artin_localEuler F E P Q _ (IsArithFrobAt.arithFrobAt (𝓞 F) Gal(E/F) Q) s

end ArtinMatthews.AbelianLocal
