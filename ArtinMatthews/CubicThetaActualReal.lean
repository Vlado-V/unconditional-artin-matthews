module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicReciprocityNonprincipalConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! Reality of the actual cubic theta coefficients, at every natural index.
The proof conjugates the finite ideal norm fiber, including conductor ideals.
-/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths

local notation "EO" => HeckeFamily.O

private instance : IsPrincipalIdealRing EO :=
  IsCyclotomicExtension.Rat.three_pid HeckeFamily.K

/-- Elementwise anti-conjugation descends to the actual ideal character. -/
theorem cubicNumeratorThetaIdeal_conjugate (A : ℤ) (hA : A ≠ 0) (I : Ideal EO) :
    thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
      (I.map heckeIntegerConjugation.toRingHom) =
    star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) I) := by
  by_cases hI : I = ⊥
  · subst I
    rw [Ideal.map_bot]
    change thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) 0 =
      star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) 0)
    have hz := thetaIdealCharacter_zero (cubicNumeratorHeckeCharacter A hA)
    exact hz.trans ((congrArg star hz).trans (star_zero ℂ)).symm
  let z : EO := Submodule.IsPrincipal.generator I
  have hz : z ≠ 0 := by
    intro h
    apply hI
    rw [← Ideal.span_singleton_generator I]
    change Ideal.span {z} = ⊥
    simp [h]
  have hcz : heckeIntegerConjugation z ≠ 0 :=
    fun h => hz (heckeIntegerConjugation.injective (h.trans (map_zero _).symm))
  rw [← Ideal.span_singleton_generator I]
  change thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
      ((Ideal.span {z}).map heckeIntegerConjugation.toRingHom) =
    star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) (Ideal.span {z}))
  rw [Ideal.map_span, Set.image_singleton]
  change thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA)
      (Ideal.span {heckeIntegerConjugation z}) =
    star (thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) (Ideal.span {z}))
  rw [thetaIdealCharacter_span _ hcz, thetaIdealCharacter_span _ hz]
  exact cubicNumeratorHeckeCharacter_element_conjugate A hA z

/-- Every actual coefficient is fixed by complex conjugation; no exclusion
of ramified primes or non-coprime indices is necessary. -/
theorem cubicNumeratorThetaCoeff_conjugate (A : ℤ) (hA : A ≠ 0) (n : ℕ) :
    star (idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n) =
      idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n :=
  idealThetaCoeff_conj_of_ideal_conjugation _ heckeIntegerConjugation
    (cubicNumeratorThetaIdeal_conjugate A hA) n

/-- The real-part sequence is exactly the complex ideal-sum sequence. -/
theorem cubicNumeratorThetaCoeff_real (A : ℤ) (hA : A ≠ 0) (n : ℕ) :
    ((idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n).re : ℂ) =
      idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n :=
  idealThetaCoeff_re_of_ideal_conjugation _ heckeIntegerConjugation
    (cubicNumeratorThetaIdeal_conjugate A hA) n

end ArtinMatthews
