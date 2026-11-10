module

public import ArtinMatthews.EisensteinAngularArch
public import ArtinMatthews.EisensteinAngularField
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.PrincipalAngularCorrection
public import ArtinMatthews.SourceGaussCharacter
public import ArtinMatthews.SourcePrimeIdealFactorization
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

/-! The exterior angular character on actual fractional ideals, with
the genuine oriented archimedean character on field units. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain AngularLambda AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical BigOperators nonZeroDivisors

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "P₀" => HeightOneSpectrum (𝓞 F)
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

private theorem angularExteriorPrime_norm (P : P₀) (hP : P ∉ S) :
    ‖cyclotomicAngularIdeal hζ P.asIdeal‖ = 1 := by
  apply cyclotomicAngularIdeal_norm hζ P.asIdeal P.ne_bot
  apply principalAngular_prime_coprime_of_not_le P
  intro hle
  have h3 : (3:𝓞 F) ∈ P.asIdeal := hle (Ideal.mem_span_singleton_self _)
  apply source_exterior_six_not_mem F S₀ P hP
  simpa only [show (2:𝓞 F) * 3 = 6 by norm_num] using P.asIdeal.mul_mem_left 2 h3

def sourceReflectionAngularPrime (P : P₀) : ℂˣ :=
  if hP : P ∈ S then 1 else
    Units.mk0 (cyclotomicAngularIdeal hζ P.asIdeal) (by
      intro h0
      have h := angularExteriorPrime_norm F hζ S₀ P hP
      rw [h0,norm_zero] at h
      exact zero_ne_one h)

theorem sourceReflectionAngularPrime_of_notMem (P : P₀) (hP : P ∉ S) :
    (sourceReflectionAngularPrime F hζ S₀ P : ℂ) = cyclotomicAngularIdeal hζ P.asIdeal := by
  rw [sourceReflectionAngularPrime,dif_neg hP]
  rfl

theorem sourceReflectionAngularPrime_norm (P : P₀) :
    ‖(sourceReflectionAngularPrime F hζ S₀ P : ℂ)‖ = 1 := by
  by_cases hP : P ∈ S
  · rw [sourceReflectionAngularPrime,dif_pos hP,Units.val_one,norm_one]
  · rw [sourceReflectionAngularPrime_of_notMem F hζ S₀ P hP]
    exact angularExteriorPrime_norm F hζ S₀ P hP

private def angularOrderProduct : Multiplicative (P₀ →₀ ℤ) →* ℂˣ where
  toFun e := e.toAdd.prod fun P n => sourceReflectionAngularPrime F hζ S₀ P ^ n
  map_one' := Finsupp.prod_zero_index
  map_mul' x y := by
    change (x.toAdd + y.toAdd).prod _ = x.toAdd.prod _ * y.toAdd.prod _
    exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

def sourceReflectionAngularIdealHom : FractionalIdealGroup F →* ℂˣ :=
  (angularOrderProduct F hζ S₀).comp
    (FractionalIdealGroup.factorizationEquiv (K := F)).symm.toMonoidHom

theorem sourceReflectionAngularIdealHom_prime (P : P₀) :
    sourceReflectionAngularIdealHom F hζ S₀ (FractionalIdealGroup.prime P) =
      sourceReflectionAngularPrime F hζ S₀ P := by
  let E := FractionalIdealGroup.factorizationEquiv (K := F)
  have hE : E.symm (FractionalIdealGroup.prime P) =
      Multiplicative.ofAdd (Finsupp.single P (1:ℤ)) := by
    apply E.injective
    rw [E.apply_symm_apply]
    change _ = (Finsupp.single P (1:ℤ)).prod
      (fun Q n => FractionalIdealGroup.prime Q ^ n)
    rw [Finsupp.prod_single_index (by simp),zpow_one]
  change angularOrderProduct F hζ S₀ (E.symm _) = _
  rw [hE]
  change (Finsupp.single P (1:ℤ)).prod
      (fun Q n => sourceReflectionAngularPrime F hζ S₀ Q ^ n) = _
  rw [Finsupp.prod_single_index (by simp),zpow_one]

theorem sourceReflectionAngularIdealHom_primeExponentIdeal (e : SourcePrimeExponents F S₀) :
    (sourceReflectionAngularIdealHom F hζ S₀
      (integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
        (sourcePrimeExponentIdeal_ne_bot F S₀ e)) : ℂ) =
      cyclotomicAngularIdeal hζ (sourcePrimeExponentIdeal F S₀ e) := by
  have hI : integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
        (sourcePrimeExponentIdeal_ne_bot F S₀ e) =
      ∏ P ∈ e.support, FractionalIdealGroup.prime P.val ^ e P := by
    apply Units.ext
    change (sourcePrimeExponentIdeal F S₀ e : FI) = _
    simp only [Units.coe_prod,Units.val_pow_eq_pow_val,FractionalIdealGroup.prime,Units.val_mk0]
    change FractionalIdeal.coeIdealHom (𝓞 F)⁰ F
      (∏ P ∈ e.support, P.val.asIdeal ^ e P) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro P _
    exact map_pow (FractionalIdeal.coeIdealHom (𝓞 F)⁰ F) P.val.asIdeal (e P)
  rw [hI, map_prod, Units.coe_prod, sourcePrimeExponentIdeal, Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro P _
  rw [map_pow, Units.val_pow_eq_pow_val, sourceReflectionAngularIdealHom_prime,
    sourceReflectionAngularPrime_of_notMem F hζ S₀ P.val P.property, map_pow]

theorem sourceReflectionAngularIdealHom_integral_eq_of_exterior (I : Ideal (𝓞 F))
    (hI : I ∈ exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀))) :
    (sourceReflectionAngularIdealHom F hζ S₀ (integralIdealFractionalUnit I hI.1) : ℂ) =
      cyclotomicAngularIdeal hζ I := by
  let e := sourceExteriorIdealExponents F S₀ ⟨I,hI⟩
  have h : sourcePrimeExponentIdeal F S₀ e = I :=
    sourceExteriorIdealExponents_recover F S₀ ⟨I,hI⟩
  have hu : integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
      (sourcePrimeExponentIdeal_ne_bot F S₀ e) = integralIdealFractionalUnit I hI.1 := by
    apply Units.ext
    exact congrArg (fun J : Ideal (𝓞 F) => (J : FI)) h
  rw [← hu, sourceReflectionAngularIdealHom_primeExponentIdeal, h]

theorem sourceReflectionAngularIdealHom_norm (I : FractionalIdealGroup F) :
    ‖(sourceReflectionAngularIdealHom F hζ S₀ I : ℂ)‖ = 1 := by
  let E := FractionalIdealGroup.factorizationEquiv (K := F)
  let e := (E.symm I).toAdd
  change ‖((∏ P ∈ e.support, sourceReflectionAngularPrime F hζ S₀ P ^ e P : ℂˣ) : ℂ)‖ = 1
  simp only [Units.coe_prod,Units.val_zpow_eq_zpow_val,norm_prod,norm_zpow,
    sourceReflectionAngularPrime_norm,one_zpow,Finset.prod_const_one]

def sourceReflectionAngularInfinityExponent (v : InfinitePlace F) : ℤ := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact angularInfinityExponent F v

theorem sourceReflectionAngularInfinityExponent_sign (v : InfinitePlace F) :
    sourceReflectionAngularInfinityExponent F hζ v = 1 ∨
      sourceReflectionAngularInfinityExponent F hζ v = -1 := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact angularInfinityExponent_eq_one_or_neg_one F v

def sourceReflectionAngularField : Fˣ →* ℂˣ := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact Units.map (complexAngularHom.toMonoidHom.comp
    (baseComplexEmbedding.toMonoidHom.comp (Algebra.norm BaseField)))

theorem sourceReflectionAngularField_val (a : Fˣ) :
    letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
    (sourceReflectionAngularField F hζ a : ℂ) = angularArchimedean F (a:F) := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact (angularArchimedean_eq_norm F (a:F)).symm

theorem sourceReflectionAngularField_place_product (a : Fˣ) :
    (sourceReflectionAngularField F hζ a : ℂ) =
      ∏ v : InfinitePlace F, complexAngular (v.embedding (a:F)) ^
        sourceReflectionAngularInfinityExponent F hζ v := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact (sourceReflectionAngularField_val F hζ a).trans (angularArchimedean_place_product F (a:F))

theorem sourceReflectionAngularField_norm (a : Fˣ) :
    ‖(sourceReflectionAngularField F hζ a : ℂ)‖ = 1 := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  change ‖complexAngular (baseComplexEmbedding (Algebra.norm BaseField (a:F)))‖ = 1
  exact complexAngular_norm (Units.map
    (baseComplexEmbedding.toMonoidHom.comp (Algebra.norm BaseField)) a).ne_zero

end
end ArtinMatthews.VaryingKummerAnalytic
