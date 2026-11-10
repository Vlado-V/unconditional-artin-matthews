module

public import ArtinMatthews.SourceQuadraticPrimitiveProduct
public import ArtinMatthews.SourceQuadraticClassFactorization
public import ArtinMatthews.SourceQuadraticConductorProduct
public import ArtinMatthews.SourceQuadraticPrimitive
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

/-! The primitive product conductor on actual fixed ray-class slices. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticConductor_product_of_rayClass_eq (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support)
    (hclass : sourcePrimeExponentRayClass F S₀ e = sourcePrimeExponentRayClass F S₀ f) :
    sourceQuadraticConductor F S₀ hζ (e + f) =
      sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f :=
  sourceQuadraticConductor_eq_product_of_class_eq F S₀ hζ e f he hf hd
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ e f hclass)

variable [IsTotallyComplex F]

theorem sourceQuadraticRayClass_primitive_product (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support)
    (hclass : sourcePrimeExponentRayClass F S₀ e = sourcePrimeExponentRayClass F S₀ f) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals
        (sourceQuadraticRayCharacter F S₀ hζ (e + f)).residue ∧
      sourceQuadraticConductor F S₀ hζ (e + f) =
        sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f ∧
      (let m := integralIdealRayModulus (sourceQuadraticProductModulus F S₀ e f)
          (sourceQuadraticProductModulus_ne_bot F S₀ e f)
       ((sourceQuadraticRayCharacter F S₀ hζ (e + f)).idealHom.comp
           (RayClass.primeToModulusIdeals m).subtype) =
         ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom.comp
           (RayClass.primeToModulusIdeals m).subtype) *
         ((sourceQuadraticRayCharacter F S₀ hζ f).idealHom.comp
           (RayClass.primeToModulusIdeals m).subtype)) :=
  ⟨sourceQuadraticRayCharacter_primitive F S₀ hζ _,
    sourceQuadraticConductor_product_of_rayClass_eq F S₀ hζ e f he hf hd hclass,
    sourceQuadraticPrimitive_product_agreement F S₀ hζ e f he hf hd⟩

end
end ArtinMatthews.SourceEulerAssembly
