module

public import ArtinMatthews.SLocalAnalyticWeil
public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.StandardTameFiniteWeil
public import ArtinMatthews.AdelicWeilFiniteProducts
public import ArtinMatthews.CyclotomicSourceWeil
public import ArtinMatthews.StandardComplexWeil
public import ArtinMatthews.StandardFiniteUnitWeil
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

/-! The actual global analytic product isolates the quadratic Gauss
factor of an exterior prime generator. All other exterior factors are
proved to be one from the generator's genuine valuations. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open AngularLambda VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]

local instance globalGeneratorQuotientField (P : HeightOneSpectrum (𝓞 F)) :
    Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance globalGeneratorQuotientFinite (P : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance globalGeneratorQuotientFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem standardNormalizedWeil_prime_eq_SInverse
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : standardWeilBadPlaces F ⊆ S)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ S) (a : Fˣ)
    (hunit : ∀ Q : HeightOneSpectrum (𝓞 F), Q ∉ S → Q ≠ P → Q.valuation F (a : F) = 1) :
    standardNormalizedWeil F a⁻¹ (.inr P) =
      (sLocalAnalyticWeil F S (sLocalGlobalClassMap F 2 S a⁻¹))⁻¹ := by
  let T : Finset (ArchimedeanAdeles.Construction.Places F) := S.image Sum.inr
  have hPT : Sum.inr P ∉ T := by
    simpa only [T, Finset.mem_image, Sum.inr.injEq, exists_eq_right] using hP
  have hout : ∀ w ∉ insert (Sum.inr P) T, standardNormalizedWeil F a⁻¹ w = 1 := by
    intro w hw
    cases w with
    | inl v => exact standardNormalizedWeil_infinite F v a⁻¹
    | inr Q =>
        have hQP : Q ≠ P := by
          intro he
          subst Q
          exact hw (Finset.mem_insert_self _ _)
        have hQS : Q ∉ S := by
          intro hq
          exact hw (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Q, hq, rfl⟩))
        apply standardNormalizedWeil_finite_unit F Q a⁻¹
        · exact fun hq => hQS (hS hq)
        · simp only [Units.val_inv_eq_inv_val, map_inv₀, hunit Q hQS hQP, inv_one]
  have he := standardNormalizedWeil_punctured F a⁻¹ T (Sum.inr P) hPT hout
  have hp : (∏ w ∈ T, standardNormalizedWeil F a⁻¹ w) =
      sLocalAnalyticWeil F S (sLocalGlobalClassMap F 2 S a⁻¹) := by
    rw [sLocalAnalyticWeil_globalClass]
    dsimp only [T]
    rw [Finset.prod_image (fun _ _ _ _ h => Sum.inr_injective h)]
    exact (Finset.prod_coe_sort S (fun v => standardNormalizedWeil F a⁻¹ (.inr v))).symm
  exact he.trans (congrArg Inv.inv hp)

theorem sourceGeneratorWeil_eq_SInverse
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ principalizingSet S₀)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    standardNormalizedWeil F (generatorFieldUnit S₀ P a ha)⁻¹ (.inr P) =
      (sLocalAnalyticWeil F (principalizingSet S₀)
        (sLocalGlobalClassMap F 2 (principalizingSet S₀) (generatorFieldUnit S₀ P a ha)⁻¹))⁻¹ := by
  apply standardNormalizedWeil_prime_eq_SInverse F _ hS P hP
  intro Q hQ hQP
  exact exterior_generator_other_valuation S₀ P a ha Q hQ hQP

theorem sourceGeneratorGammaThree_eq_SInverse
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ principalizingSet S₀)
    {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase S₀ P hP a ha) 3 =
      (sLocalAnalyticWeil F (principalizingSet S₀)
        (sLocalGlobalClassMap F 2 (principalizingSet S₀) (generatorFieldUnit S₀ P a ha)⁻¹))⁻¹ := by
  have hbad : P ∉ StandardAdelic.traceBadPlaces F :=
    fun h => hP (hS (Finset.mem_union_left _ h))
  rw [← sourceGeneratorWeil_eq_angularGammaThree F S₀ P hζ hP a ha hbad hsix]
  exact sourceGeneratorWeil_eq_SInverse F S₀ hS P hP a ha

end

end ArtinMatthews.QuadraticWeil
