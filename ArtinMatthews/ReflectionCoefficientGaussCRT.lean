module

public import ArtinMatthews.ReflectionSquarefreeGaussCRT
public import ArtinMatthews.ReflectionCoefficientRow


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global gamma2 in the literal B_m is exactly the product
of local standard source Gauss sums with its directed CRT characters. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open SIntegerFourier StandardAdelic SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

private theorem sourceGauss_modulus_congr
    (T : Finset (HeightOneSpectrum (𝓞 F))) (a b : PrincipalIntegerRing T)
    (hab : a = b) (ha : a ≠ 0) (hb : b ≠ 0) (f : PrincipalIntegerRing T → ℂ) :
    (∑' x : (PrincipalIntegerRing T) ⧸ Ideal.span {a}, f (Quotient.out x) *
      sIntegerQuotientPhase F (principalizingSet T) a ha x) =
    ∑' x : (PrincipalIntegerRing T) ⧸ Ideal.span {b}, f (Quotient.out x) *
      sIntegerQuotientPhase F (principalizingSet T) b hb x := by
  subst b
  rfl

theorem reflectionSquarefreeExponent_support_one (c : ReflectionSquarefreeExponents F S₀)
    (P : c.val.support) : c.val P.val = 1 := by
  have hn := Finsupp.mem_support_iff.mp P.property
  have hb := c.property P.val
  omega

theorem reflectionSquarefreeGenerator_support (c : ReflectionSquarefreeExponents F S₀) :
    sourcePrimeExponentGenerator F hζ S₀ c.val =
      ∏ P : c.val.support, sourceAllowedPrimeGenerator F hζ S₀ P.val ^ (1 : ℕ) := by
  unfold sourcePrimeExponentGenerator Finsupp.prod
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro P _
  rw [reflectionSquarefreeExponent_support_one F S₀ c P]

theorem reflectionSquarefreeResidueValue_support (c : ReflectionSquarefreeExponents F S₀)
    (x : sourceRing F S₀) :
    reflectionExponentResidueValue F hζ S₀ c.val x =
      sourceSexticWeight (sourceHilbertSeed F S₀) (fun P : c.val.support => P.val.val)
        (fun P => P.val.property) (fun P => sourceAllowedPrimeGenerator F hζ S₀ P.val)
        (fun P => sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val)
        (fun P => reflectionPrimeCharacters F hζ S₀ P.val) (fun _ => 1) x := by
  have h := sourcePrimeExponentWeight_eq_sourceSexticWeight F hζ S₀
    (reflectionPrimeCharacters F hζ S₀) c.val x c.val.support (fun _ h => h)
  have he : (fun P : c.val.support => c.val P.val) = fun _ => 1 :=
    funext (reflectionSquarefreeExponent_support_one F S₀ c)
  rw [he] at h
  exact h

def reflectionGammaTwoCRTProduct (c : ReflectionSquarefreeExponents F S₀) : ℂ :=
  let T := sourceHilbertSeed F S₀
  let P : c.val.support → HeightOneSpectrum (𝓞 F) := fun P => P.val.val
  let a := fun P : c.val.support => sourceAllowedPrimeGenerator F hζ S₀ P.val
  let ha := fun P : c.val.support => sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val
  let χ := fun P : c.val.support => reflectionPrimeCharacters F hζ S₀ P.val
  (∏ i, (generatorResidueCharacter T (P i) i.val.property (a i) (ha i) (χ i)
    (Ideal.Quotient.mk _ (sourcePrimeCofactor T a (fun _ => 1) i))) ^ 2) *
    ∏ i, residueSourceTau T (P i) i.val.property (a i) (ha i) (χ i ^ 2)

theorem reflectionGammaTwo_eq_crt (c : ReflectionSquarefreeExponents F S₀) :
    reflectionGammaTwo F hζ S₀ c.val =
      reflectionGammaTwoCRTProduct F hζ S₀ c /
        (Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) := by
  let T := sourceHilbertSeed F S₀
  let P : c.val.support → HeightOneSpectrum (𝓞 F) := fun P => P.val.val
  let hP : Pairwise fun i j => P i ≠ P j := by
    intro i j hij he
    exact hij (Subtype.ext (Subtype.ext he))
  let a := fun P : c.val.support => sourceAllowedPrimeGenerator F hζ S₀ P.val
  let ha := fun P : c.val.support => sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val
  let χ := fun P : c.val.support => reflectionPrimeCharacters F hζ S₀ P.val
  have h := reflectionSquarefreeGauss_crt T P hP (fun P => P.val.property) a ha χ
  unfold reflectionGammaTwo
  dsimp only
  congr 1
  calc
    _ = ∑' x : (sourceRing F S₀) ⧸ Ideal.span {∏ i, a i ^ (1 : ℕ)},
        (sourceSexticWeight T P (fun P => P.val.property) a ha χ (fun _ => 1)
          (Quotient.out x)) ^ 2 *
          sIntegerQuotientPhase F (sourceHilbertSet F S₀) (∏ i, a i ^ (1 : ℕ))
            (generatorProduct_ne_zero T P a ha (fun _ => 1)) x := by
      simp only [reflectionSquarefreeResidueValue_support F hζ S₀ c]
      exact sourceGauss_modulus_congr F T _ _
        (reflectionSquarefreeGenerator_support F hζ S₀ c)
        (sourcePrimeExponentGenerator_ne_zero F hζ S₀ c.val)
        (generatorProduct_ne_zero T P a ha (fun _ => 1))
        (fun y => (sourceSexticWeight T P (fun P => P.val.property) a ha χ (fun _ => 1) y) ^ 2)
    _ = _ := h

end
end ArtinMatthews.VaryingKummerAnalytic
