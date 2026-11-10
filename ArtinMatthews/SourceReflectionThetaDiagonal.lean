module

public import ArtinMatthews.SourceReflectionWholeThetaCharacter
public import ArtinMatthews.SourceReflectionThetaDictionary
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

/-! The whole reflected phase of a field diagonal is its exterior
fractional-ideal character, retaining both finite ray corrections. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open IsDedekindDomain AngularLambda AllowedGenerators SourcePhysical QuadraticWeil
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceReflectionArchAngularCharacter_diagonal
    (T : Finset (HeightOneSpectrum (𝓞 F))) (a : Fˣ) :
    sourceReflectionArchAngularCharacter F hζ (sWholeDiagonal F T a).1 =
      (sourceReflectionAngularField F hζ a)⁻¹ := by
  apply Units.ext
  rw [sourceReflectionArchAngularCharacter_val, sourceReflectionAngularField_inv_place_product]
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (fun z : ℂ => complexAngular z ^ (-sourceReflectionAngularInfinityExponent F hζ v))
  rw [ringEquivComplexOfIsComplex_apply]
  change extensionEmbedding v (((WithAbs.equiv v.1).symm (a:F) : WithAbs v.1) : v.Completion) =
    v.embedding (a:F)
  rw [extensionEmbedding_coe, RingEquiv.apply_symm_apply]

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "G" => sixthKummerFixedIdeal S
local notation "hG" => mul_ne_zero (sixthKummerFixedIdeal_ne_zero S) (sixthKummerFixedIdeal_ne_zero S)
variable {J : Ideal (𝓞 F)}

theorem sourceReflectionWholeThetaCharacter_diagonal
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) (a : Fˣ) :
    let D := IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a)
    sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ (sWholeDiagonal F S a) =
      (sourceReflectionAngularIdealHom F hζ S₀ D)⁻¹ *
        ((sourceGaussHeckeCharacter F hζ S₀ hBad).idealHom D)⁻¹ * η.idealHom D := by
  let gauss : EvenIdealRayCharacter F (G * G) := @sourceGaussHeckeCharacter F _ _ _ ζ hζ S₀ hBad
  let D := IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a)
  let u := sourceReflectionFiniteDiagonal F S a
  let A := sourceReflectionAngularField F hζ a
  let L := sourceReflectionAngularIdealHom F hζ S₀ D
  let R := gauss.idealHom D
  let E := η.idealHom D
  have hA : sourceReflectionLocalAngularCharacter F hζ S₀ u = A / L :=
    sourceReflectionLocalAngularCharacter_diagonal F hζ S₀ a
  have hR : sourceReflectionLocalRayCharacter F S gauss hG u = R⁻¹ := by
    have h := sourceReflectionIdealRay_exteriorPrincipal F S gauss hG
      (sourceReflectionGaussModulus_support F S₀).le a
    simpa only [inv_inv] using (congrArg (fun z : ℂˣ => z⁻¹) h).symm
  have hE : sourceReflectionLocalRayCharacter F S η hJ u = E⁻¹ := by
    have h := sourceReflectionIdealRay_exteriorPrincipal F S η hJ
      (sourceReflectionTargetModulus_support F S₀ hJ hcut) a
    simpa only [inv_inv] using (congrArg (fun z : ℂˣ => z⁻¹) h).symm
  change (sourceReflectionLocalAngularCharacter F hζ S₀ u *
    sourceReflectionLocalRayCharacter F S gauss hG u /
    sourceReflectionLocalRayCharacter F S η hJ u) *
      sourceReflectionArchAngularCharacter F hζ (sWholeDiagonal F S a).1 = L⁻¹ * R⁻¹ * E
  rw [hA, hR, hE, sourceReflectionArchAngularCharacter_diagonal F hζ S a, div_inv_eq_mul]
  simp only [div_eq_mul_inv]
  change A * L⁻¹ * R⁻¹ * E * A⁻¹ = L⁻¹ * R⁻¹ * E
  calc
    _ = A * ((L⁻¹ * R⁻¹ * E) * A⁻¹) := by simp only [mul_assoc]
    _ = _ := by rw [mul_comm (L⁻¹ * R⁻¹ * E) A⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

end
end ArtinMatthews.VaryingKummerAnalytic
