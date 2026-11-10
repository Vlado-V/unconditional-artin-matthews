module

public import ArtinMatthews.CubicReciprocityBridgeIntegral
public import ArtinMatthews.CubicFrobeniusCondition
public import ArtinMatthews.CubicReciprocityBridgeCharacters
public import ArtinMatthews.CubicReciprocityBridgeFrobenius
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Actual Kummer Fourier characters evaluated on arithmetic Frobenius. -/

open scoped NumberField

namespace ArtinMatthews

open OAI OAI.ActualEisensteinCubic

local notation "EO" => OAI.ActualEisensteinCubic.O

theorem actualCubicFrobenius_radical_ratio {S : Finset ℤ}
    (P : Ideal EO) [P.IsMaximal] (Q : Ideal (𝓞 (integerCubicField S)))
    [Q.IsPrime] [Q.LiesOver P] (hg : lambda ∉ P)
    (σ : integerCubicGaloisGroup S) (hF : IsArithFrobAt EO σ Q)
    {A : ℤ} (hA : (A : EO) ∉ P) {R : integerCubicField S}
    (hR : R ^ 3 = (A : integerCubicField S)) (hR0 : R ≠ 0) :
    σ.val R / R = heckeKummerFieldEmbedding S
      (cubicChar P hg (Ideal.Quotient.mk P (A : EO)) : OAI.SevenEighths.HeckeFamily.K) := by
  let r : 𝓞 (integerCubicField S) := ⟨R, cubeRoot_isIntegral hR⟩
  have hr : r ^ 3 = algebraMap EO (𝓞 (integerCubicField S)) (A : EO) := by
    apply Subtype.ext
    change R ^ 3 = heckeKummerFieldEmbedding S (A : OAI.SevenEighths.HeckeFamily.K)
    rw [map_intCast]
    exact hR
  have h := arithFrob_cubic_symbol_action P Q hg σ hF hA hr
  have hh := congrArg (fun z : 𝓞 (integerCubicField S) => (z : integerCubicField S)) h
  change σ.val R = heckeKummerFieldEmbedding S
    (cubicChar P hg (Ideal.Quotient.mk P (A : EO)) : OAI.SevenEighths.HeckeFamily.K) * R at hh
  exact (div_eq_iff hR0).mpr hh

/-- Every actual Fourier character has one integer radicand whose genuine
cubic residue symbol gives its value on arithmetic Frobenius. -/
theorem cubicFourier_character_has_symbol {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ A : ℤ, A ≠ 0 ∧
      ∀ (P : Ideal EO) [P.IsMaximal] (Q : Ideal (𝓞 (integerCubicField S)))
        [Q.IsPrime] [Q.LiesOver P] (hg : lambda ∉ P)
        (σ : integerCubicGaloisGroup S), IsArithFrobAt EO σ Q → (A : EO) ∉ P →
        χ (Additive.ofMul σ) =
          ((heckeKummerFieldEmbedding S
            (cubicChar P hg (Ideal.Quotient.mk P (A : EO)) :
              OAI.SevenEighths.HeckeFamily.K) : integerCubicField S) : ℂ) := by
  obtain ⟨e, R, hR0, hR, hχ⟩ := cubicFourier_character_has_radical hzero χ
  let A : ℤ := cubicProductRadicand (fun i => (e i : ℕ))
  have hA0 : A ≠ 0 := by
    intro h
    have hz : R ^ 3 = 0 := by simpa only [A, h, Int.cast_zero] using hR
    exact pow_ne_zero 3 hR0 hz
  refine ⟨A, hA0, ?_⟩
  intro P hP Q hQ hQP hg σ hF hA
  rw [hχ σ, actualCubicFrobenius_radical_ratio P Q hg σ hF hA hR hR0]

/-- With the oriented cyclotomic embedding, the value is exactly the cubic
residue symbol in the complex embedding used by the Hecke theory. -/
theorem cubicFourier_character_has_prime_symbol {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ A : ℤ, A ≠ 0 ∧
      ∀ (P : Ideal EO) [P.IsMaximal] (D : EisensteinFrobeniusData S P)
        (hg : lambda ∉ P), (A : EO) ∉ P →
        χ (Additive.ofMul D.frobenius) =
          ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P (A : EO))) := by
  obtain ⟨A, hA0, hA⟩ := cubicFourier_character_has_symbol hzero χ
  refine ⟨A, hA0, ?_⟩
  intro P hP D hg hAP
  let : D.primeIdeal.IsMaximal := D.maximal
  let : D.primeIdeal.LiesOver P := D.liesOver
  exact (hA P D.primeIdeal hg D.frobenius D.frobenius_spec hAP).trans
    (coe_heckeKummerIntegersEmbedding_complex S _)

end ArtinMatthews
