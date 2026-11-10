module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.PrincipalAngularCorrection
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceQuadraticConductorProduct
public import ArtinMatthews.SourceQuadraticMultiplicativity
public import ArtinMatthews.SourceQuadraticSelfDual
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The product-radicand character agrees with the product of the two
actual characters on a proved common ray modulus. The common-ray agreement identifies its primitive inducing character. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "S" => sourceHilbertSet F S₀

def sourceQuadraticProductModulus (e f : E) : Ideal (𝓞 F) :=
  sixthKummerFixedIdeal S ^ 2 * (sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f)

theorem sourceQuadraticProductModulus_ne_bot (e f : E) :
    sourceQuadraticProductModulus F S₀ e f ≠ ⊥ :=
  mul_ne_zero (pow_ne_zero _ (sixthKummerFixedIdeal_ne_zero S))
    (mul_ne_zero (sourcePrimeExponentIdeal_ne_bot F S₀ e) (sourcePrimeExponentIdeal_ne_bot F S₀ f))

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceQuadraticConductor_dvd_fixed_exterior (e : E) (he : ∀ P, e P ≤ 1) :
    sourceQuadraticConductor F S₀ hζ e ∣
      sixthKummerFixedIdeal S * sourcePrimeExponentIdeal F S₀ e := by
  rw [sourceQuadraticConductor_factorization F S₀ hζ e he, mul_comm (sixthKummerFixedIdeal S)]
  exact mul_dvd_mul (dvd_refl _) (sourceQuadraticWildIdeal_dvd_fixed F S₀ hζ e)

theorem sourceQuadraticProductModulus_conductors (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support) :
    sourceQuadraticConductor F S₀ hζ e ∣ sourceQuadraticProductModulus F S₀ e f ∧
      sourceQuadraticConductor F S₀ hζ f ∣ sourceQuadraticProductModulus F S₀ e f ∧
      sourceQuadraticConductor F S₀ hζ (e + f) ∣ sourceQuadraticProductModulus F S₀ e f := by
  let q := sixthKummerFixedIdeal S
  let A := sourcePrimeExponentIdeal F S₀ e
  let B := sourcePrimeExponentIdeal F S₀ f
  have hm : sourceQuadraticProductModulus F S₀ e f = (q * A) * (q * B) := by
    change q ^ 2 * (A * B) = _
    rw [pow_two]
    ac_rfl
  have hs := sourceQuadraticConductor_dvd_fixed_exterior F S₀ hζ (e + f)
    (sourceQuadraticDisjoint_add_squarefree F S₀ e f he hf hd)
  rw [sourcePrimeExponentIdeal_add] at hs
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    exact (sourceQuadraticConductor_dvd_fixed_exterior F S₀ hζ e he).trans (dvd_mul_right _ _)
  · rw [hm]
    exact (sourceQuadraticConductor_dvd_fixed_exterior F S₀ hζ f hf).trans (dvd_mul_left _ _)
  · exact hs.trans (mul_dvd_mul (dvd_pow_self q (by decide : (2 : ℕ) ≠ 0)) (dvd_refl (A * B)))

omit hζ in
theorem sourceQuadraticProductModulus_outside (e f : E) (P : HeightOneSpectrum (𝓞 F))
    (hP : P ∉ (integralIdealFiniteModulus (sourceQuadraticProductModulus F S₀ e f)
      (sourceQuadraticProductModulus_ne_bot F S₀ e f)).support) : P ∉ S := by
  have hn : ¬ P.asIdeal ∣ sourceQuadraticProductModulus F S₀ e f :=
    mt (integralIdealFiniteModulus_mem_support _ _ P).mpr hP
  intro hPS
  apply hn
  have hq : P.asIdeal ∣ sixthKummerFixedIdeal S :=
    (dvd_pow_self P.asIdeal (sixthLocalHenselDepth_pos P).ne').trans
      (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ sixthLocalHenselDepth v) hPS)
  have hqq : sixthKummerFixedIdeal S ∣ sixthKummerFixedIdeal S ^ 2 :=
    dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0)
  exact hq.trans (hqq.trans (dvd_mul_right _ _))

variable [IsTotallyComplex F]

theorem sourceQuadraticPrimitive_product_agreement (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support) :
    let m := integralIdealRayModulus (sourceQuadraticProductModulus F S₀ e f)
      (sourceQuadraticProductModulus_ne_bot F S₀ e f)
    ((sourceQuadraticRayCharacter F S₀ hζ (e + f)).idealHom.comp (RayClass.primeToModulusIdeals m).subtype) =
      ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom.comp (RayClass.primeToModulusIdeals m).subtype) *
        ((sourceQuadraticRayCharacter F S₀ hζ f).idealHom.comp (RayClass.primeToModulusIdeals m).subtype) := by
  let M := sourceQuadraticProductModulus F S₀ e f
  let hM := sourceQuadraticProductModulus_ne_bot F S₀ e f
  let m := integralIdealRayModulus M hM
  obtain ⟨heM, hfM, hsM⟩ := sourceQuadraticProductModulus_conductors F S₀ hζ e f he hf hd
  apply RayClass.primeToModulusIdeals_hom_ext m
  intro P hP
  have hn : ¬ P.asIdeal ∣ M := mt (integralIdealFiniteModulus_mem_support M hM P).mpr hP
  have hPM : IsCoprime P.asIdeal M :=
    principalAngular_prime_coprime_of_not_le P M (fun h => hn (Ideal.dvd_iff_le.mpr h))
  have hPe := hPM.of_isCoprime_of_dvd_right heM
  have hPf := hPM.of_isCoprime_of_dvd_right hfM
  have hPs := hPM.of_isCoprime_of_dvd_right hsM
  let p : SourceExteriorPrime F S₀ := ⟨P, sourceQuadraticProductModulus_outside F S₀ e f P hP⟩
  have hI : sourcePrimeExponentIdeal F S₀ (Finsupp.single p 1) = P.asIdeal := by
    change (Finsupp.single p (1 : ℕ)).prod (fun Q n => Q.val.asIdeal ^ n) = _
    rw [Finsupp.prod_single_index (a := p) (b := 1)
      (h := fun Q n => Q.val.asIdeal ^ n) (pow_zero P.asIdeal), pow_one]
  have hc := sourceQuadraticRayCharacter_product_exterior F S₀ hζ e f he hf hd (Finsupp.single p 1)
  rw [hI, sourceQuadraticRayCharacter_star_allCoefficient] at hc
  simp only [EvenIdealRayCharacter.allCoefficient, dite_eq_left P.ne_bot,
    ite_eq_left hPe, ite_eq_left hPf, ite_eq_left hPs] at hc
  change (sourceQuadraticRayCharacter F S₀ hζ (e + f)).idealHom (FractionalIdealGroup.prime P) =
    (sourceQuadraticRayCharacter F S₀ hζ e).idealHom (FractionalIdealGroup.prime P) *
      (sourceQuadraticRayCharacter F S₀ hζ f).idealHom (FractionalIdealGroup.prime P)
  exact Units.ext hc

end
end ArtinMatthews.SourceEulerAssembly
