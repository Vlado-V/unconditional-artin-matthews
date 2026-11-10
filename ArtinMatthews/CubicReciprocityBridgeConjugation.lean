module

public import ArtinMatthews.CubicReciprocityBridgeIntegral
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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

/-! Conjugating actual primes and Frobenius lifts in the cubic Kummer field. -/
noncomputable section
open scoped NumberField Pointwise

namespace ArtinMatthews

/-- The oriented integral embedding intertwines the actual complex
conjugation with Eisenstein conjugation. -/
theorem heckeKummerIntegersEmbedding_conj (S : Finset ℤ)
    (a : OAI.ActualEisensteinCubic.O) :
    cubicKummerConjugation (integerCubicBases S) • heckeKummerIntegersEmbedding S a =
      heckeKummerIntegersEmbedding S (OAI.ActualEisensteinCubic.conjO a) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((cubicKummerConjugation (integerCubicBases S)
    (heckeKummerIntegersEmbedding S a : integerCubicField S) : integerCubicField S) : ℂ) = _
  rw [coe_cubicKummerConjugation]
  change star (((heckeKummerIntegersEmbedding S a : 𝓞 (integerCubicField S)) :
    integerCubicField S) : ℂ) =
      (((heckeKummerIntegersEmbedding S (OAI.ActualEisensteinCubic.conjO a) :
        𝓞 (integerCubicField S)) : integerCubicField S) : ℂ)
  rw [coe_heckeKummerIntegersEmbedding_complex, coe_heckeKummerIntegersEmbedding_complex,
    OAI.ActualEisensteinCubic.eisEmbedding_conjO]

/-- The prime induced in the Eisenstein integers is conjugated by the
Eisenstein involution when the prime upstairs is complex-conjugated. -/
theorem conjugate_prime_under_eisenstein (S : Finset ℤ)
    (Q : Ideal (𝓞 (integerCubicField S))) :
    (cubicKummerConjugation (integerCubicBases S) • Q).under OAI.ActualEisensteinCubic.O =
      (Q.under OAI.ActualEisensteinCubic.O).comap OAI.ActualEisensteinCubic.conjO.toRingHom := by
  ext a
  change heckeKummerIntegersEmbedding S a ∈
    cubicKummerConjugation (integerCubicBases S) • Q ↔
      heckeKummerIntegersEmbedding S (OAI.ActualEisensteinCubic.conjO a) ∈ Q
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, cubicKummerConjugation_inv,
    heckeKummerIntegersEmbedding_conj]

/-- Transport actual integral Frobenius data by an actual field automorphism. -/
def IntegralFrobeniusData.conjugate {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} (D : IntegralFrobeniusData K p) (τ : Gal(K/ℚ)) :
    IntegralFrobeniusData K p where
  primeIdeal := τ • D.primeIdeal
  maximal := by
    let : D.primeIdeal.IsMaximal := D.maximal
    rw [Ideal.pointwise_smul_def]
    exact D.maximal.map_bijective _
      (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) τ).bijective
  under_eq := by rw [Ideal.under_smul, D.under_eq]
  frobenius := τ * D.frobenius * τ⁻¹
  frobenius_spec := D.frobenius_spec.conj τ

/-- Complex conjugation inverts the actual relative cubic Frobenius. -/
theorem relativeCubicFrobenius_conjugate {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
    (D : IntegralFrobeniusData (integerCubicField S) p) (hp3 : p % 3 = 1) :
    relativeCubicFrobenius
      (D.conjugate (cubicKummerConjugation (integerCubicBases S))) hp3 =
        (relativeCubicFrobenius D hp3)⁻¹ := by
  apply Subtype.ext
  exact cubicKummer_conjugation_inverts (relativeCubicFrobenius D hp3).property

/-- The conjugate prime contributes the inverse value of every actual
Fourier character. -/
theorem cubicFourier_conjugateFrobenius {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
    (D : IntegralFrobeniusData (integerCubicField S) p) (hp3 : p % 3 = 1)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    χ (Additive.ofMul (relativeCubicFrobenius
      (D.conjugate (cubicKummerConjugation (integerCubicBases S))) hp3)) =
      (χ (Additive.ofMul (relativeCubicFrobenius D hp3)))⁻¹ := by
  rw [relativeCubicFrobenius_conjugate]
  exact χ.map_neg_eq_inv _

end ArtinMatthews
