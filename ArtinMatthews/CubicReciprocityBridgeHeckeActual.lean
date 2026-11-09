module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacter
public import ArtinMatthews.CubicReciprocityBridgeHeckePrime
public import ArtinMatthews.CubicReciprocityBridgeRationalSymbol
public import ArtinMatthews.CubicReciprocityBridgeConjugation
public import ArtinMatthews.CubicReciprocityBridgeConductorSupport
public import ArtinMatthews.CubicThetaPrimeFiber


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual finite-conductor Hecke character of a cubic Kummer character

The supplied cubic numerator character and its proved supplementary laws
supply the finite conductor. The Euler comparison identifies its actual
prime ideal values with arithmetic Frobenius on the concrete Kummer field.
-/

noncomputable section
open scoped NumberField BigOperators
namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths
local notation "EO" => HeckeFamily.O

/-- Every character occurring in the actual finite Fourier expansion is
represented by a genuine finite-conductor Hecke character. Nonconstant
Fourier characters give nonprincipal Hecke characters. -/
theorem cubicFourier_character_has_heckeCharacter {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ (A : ℤ) (hA : A ≠ 0),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (cubicNumeratorHeckeCharacter A hA).modulus = Ideal.span {9 * (A : EO)} ∧
      (cubicNumeratorHeckeCharacter A hA).modulus.absNorm = 81 * A.natAbs ^ 2 ∧
      (χ ≠ 0 → (cubicNumeratorHeckeCharacter A hA).residue ≠ 1) ∧
      ∀ (P : Ideal EO) [P.IsMaximal] (D : EisensteinFrobeniusData S P)
        (_hg : lambda ∉ P), (A : EO) ∉ P →
        thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) P =
          χ (Additive.ofMul D.frobenius) := by
  obtain ⟨e, R, hR0, hR, hrep⟩ := cubicFourier_character_has_radical hzero χ
  let A : ℤ := cubicProductRadicand (fun i => (e i : ℕ))
  have hA0 : A ≠ 0 := by
    intro h
    have hz : R ^ 3 = 0 := by simpa only [A, h, Int.cast_zero] using hR
    exact pow_ne_zero 3 hR0 hz
  refine ⟨A, hA0, cubicProductRadicand_dvd_product_square e, rfl,
    cubicNumeratorHeckeModulus_absNorm A, ?_, ?_⟩
  · intro hχ
    exact cubicNumeratorHeckeCharacter_nonprincipal_of_fourier χ hχ hA0 hR0 hR hrep
  · intro P hP D hg hAP
    rw [cubicNumeratorHeckeCharacter_prime A hA0 P hg hAP]
    symm
    rw [hrep D.frobenius]
    let : D.primeIdeal.IsMaximal := D.maximal
    let : D.primeIdeal.LiesOver P := D.liesOver
    rw [actualCubicFrobenius_radical_ratio P D.primeIdeal hg D.frobenius
      D.frobenius_spec hAP hR hR0]
    exact coe_heckeKummerIntegersEmbedding_complex S _

/-- The same identification at the original rational prime Frobenius.
The only excluded rational primes divide the explicit finite integer `3A`. -/
theorem cubicFourier_character_has_rational_heckeCharacter {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ (A : ℤ) (hA : A ≠ 0),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (cubicNumeratorHeckeCharacter A hA).modulus.absNorm = 81 * A.natAbs ^ 2 ∧
      (χ ≠ 0 → (cubicNumeratorHeckeCharacter A hA).residue ≠ 1) ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1)
        (D : IntegralFrobeniusData (integerCubicField S) p),
        ¬ (p : ℤ) ∣ A →
        thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) D.eisensteinPrime =
          χ (Additive.ofMul (relativeCubicFrobenius D hp3)) := by
  obtain ⟨A, hA, hdiv, _, hnorm, hnontrivial, hprime⟩ :=
    cubicFourier_character_has_heckeCharacter hzero χ
  refine ⟨A, hA, hdiv, hnorm, hnontrivial, ?_⟩
  intro p hp hp3 D hAp
  let : D.eisensteinPrime.IsMaximal := D.eisensteinPrime_maximal
  exact hprime D.eisensteinPrime (D.toEisensteinFrobeniusData hp3)
    (D.eisensteinPrime_good hp3) (D.eisenstein_int_not_mem hAp)

/-- The two conjugate Eisenstein prime ideals give the two-dimensional
induced trace, using the actual conjugate Frobenius lift. -/
theorem cubicFourier_character_has_rational_heckeTrace {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ (A : ℤ) (hA : A ≠ 0),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (cubicNumeratorHeckeCharacter A hA).modulus.absNorm = 81 * A.natAbs ^ 2 ∧
      (χ ≠ 0 → (cubicNumeratorHeckeCharacter A hA).residue ≠ 1) ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1)
        (D : IntegralFrobeniusData (integerCubicField S) p),
        ¬ (p : ℤ) ∣ A →
        thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) D.eisensteinPrime +
          thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
            (D.conjugate (cubicKummerConjugation (integerCubicBases S))).eisensteinPrime =
          χ (Additive.ofMul (relativeCubicFrobenius D hp3)) +
            (χ (Additive.ofMul (relativeCubicFrobenius D hp3)))⁻¹ := by
  obtain ⟨A, hA, hdiv, hnorm, hnontrivial, hprime⟩ :=
    cubicFourier_character_has_rational_heckeCharacter hzero χ
  refine ⟨A, hA, hdiv, hnorm, hnontrivial, ?_⟩
  intro p hp hp3 D hAp
  rw [hprime p hp3 D hAp,
    hprime p hp3 (D.conjugate (cubicKummerConjugation (integerCubicBases S))) hAp,
    cubicFourier_conjugateFrobenius]

/-- The original finite base support suffices for every Fourier character;
no character-dependent extra primes are introduced. -/
theorem cubicFourier_character_has_uniform_heckeTrace {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ (A : ℤ) (hA : A ≠ 0),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (cubicNumeratorHeckeCharacter A hA).modulus.absNorm = 81 * A.natAbs ^ 2 ∧
      (χ ≠ 0 → (cubicNumeratorHeckeCharacter A hA).residue ≠ 1) ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1)
        (D : IntegralFrobeniusData (integerCubicField S) p),
        (∀ a ∈ S, ¬ (p : ℤ) ∣ a) →
        thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) D.eisensteinPrime +
          thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
            (D.conjugate (cubicKummerConjugation (integerCubicBases S))).eisensteinPrime =
          χ (Additive.ofMul (relativeCubicFrobenius D hp3)) +
            (χ (Additive.ofMul (relativeCubicFrobenius D hp3)))⁻¹ := by
  obtain ⟨A, hA, hdiv, hnorm, hnontrivial, hprime⟩ :=
    cubicFourier_character_has_rational_heckeTrace hzero χ
  refine ⟨A, hA, hdiv, hnorm, hnontrivial, ?_⟩
  intro p hp hp3 D hS
  apply hprime p hp3 D
  intro hAp
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  have hprod : (p : ℤ) ∣ ∏ a ∈ S, a := hpz.dvd_of_dvd_pow (hAp.trans hdiv)
  obtain ⟨a, ha, hpa⟩ := (hpz.dvd_finsetProd_iff (fun a : ℤ => a)).mp hprod
  exact hS a ha hpa

/-- The natural Hecke theta coefficient, rather than an independently
defined trace, is exactly the paired Kummer character at rational primes. -/
theorem cubicFourier_character_has_thetaTrace {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ (A : ℤ) (hA : A ≠ 0),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (cubicNumeratorHeckeCharacter A hA).modulus.absNorm = 81 * A.natAbs ^ 2 ∧
      (χ ≠ 0 → (cubicNumeratorHeckeCharacter A hA).residue ≠ 1) ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1)
        (D : IntegralFrobeniusData (integerCubicField S) p),
        (∀ a ∈ S, ¬ (p : ℤ) ∣ a) →
        idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) p =
          cubicTrace (χ (Additive.ofMul (relativeCubicFrobenius D hp3))) := by
  obtain ⟨A, hA, hdiv, hnorm, hnontrivial, htrace⟩ :=
    cubicFourier_character_has_uniform_heckeTrace hzero χ
  refine ⟨A, hA, hdiv, hnorm, hnontrivial, ?_⟩
  intro p hp hp3 D hS
  rw [D.idealThetaCoeff_split_prime hp3]
  exact htrace p hp3 D hS

end ArtinMatthews
