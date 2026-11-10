module

public import ArtinMatthews.SourceQuadraticClassRay
public import ArtinMatthews.SourceQuadraticLocalClasses
public import ArtinMatthews.SourcePrimeExponentProducts
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The literal exterior ideal product supplies the finite ray label.
The ray label recovers the actual local square class of its fixed
allowed generator. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain FractionalIdeal RayClass
open AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "m" => sourceQuadraticFixedModulus F S₀

def sourcePrimeExponentRayIdeal (e : E) : primeToModulusIdeals m :=
  e.prod fun P n => (primeToModulusIdeal m P.val (by
    rw [sourceQuadraticFixedModulus_support]
    exact P.property)) ^ n

theorem sourcePrimeExponentRayIdeal_coe (e : E) :
    (sourcePrimeExponentRayIdeal F S₀ e : FractionalIdealGroup F) =
      integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
        (sourcePrimeExponentIdeal_ne_bot F S₀ e) := by
  apply Units.ext
  simp only [sourcePrimeExponentRayIdeal, sourcePrimeExponentIdeal, Finsupp.prod,
    SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow,
    primeToModulusIdeal_coe, Units.coe_prod, Units.val_pow_eq_pow_val,
    integralIdealFractionalUnit, Units.val_mk0]
  change _ = (coeIdealHom (𝓞 F)⁰ F) _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro P _
  rw [map_pow]
  rfl

def sourcePrimeExponentRayClass (e : E) : SourceQuadraticRayClass F S₀ :=
  QuotientGroup.mk' (principalRayIdealSubgroup m) (sourcePrimeExponentRayIdeal F S₀ e)

theorem sourcePrimeExponentRayClass_zero : sourcePrimeExponentRayClass F S₀ 0 = 1 := by
  simp [sourcePrimeExponentRayClass, sourcePrimeExponentRayIdeal]

theorem sourcePrimeExponentRayClass_add (e f : E) :
    sourcePrimeExponentRayClass F S₀ (e + f) =
      sourcePrimeExponentRayClass F S₀ e * sourcePrimeExponentRayClass F S₀ f := by
  have h : sourcePrimeExponentRayIdeal F S₀ (e + f) =
      sourcePrimeExponentRayIdeal F S₀ e * sourcePrimeExponentRayIdeal F S₀ f :=
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  simp only [sourcePrimeExponentRayClass, h, map_mul]

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourcePrimeExponentIdeal_extended (e : E) :
    extendedIdealGroup F S₀
        (integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
          (sourcePrimeExponentIdeal_ne_bot F S₀ e)) =
      toPrincipalIdeal (sourceRing F S₀) F (sourcePrimeExponentUnit F hζ S₀ e) := by
  apply Units.ext
  calc
    _ = ((sourcePrimeExponentIdeal F S₀ e).map
        (algebraMap (𝓞 F) (sourceRing F S₀)) :
          FractionalIdeal (sourceRing F S₀)⁰ F) :=
      extendedIdealGroup_integral F S₀
        ⟨sourcePrimeExponentIdeal F S₀ e,
          mem_nonZeroDivisors_iff_ne_zero.mpr (sourcePrimeExponentIdeal_ne_bot F S₀ e)⟩
    _ = (Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e} :
          FractionalIdeal (sourceRing F S₀)⁰ F) :=
      congrArg (fun I : Ideal (sourceRing F S₀) =>
        (I : FractionalIdeal (sourceRing F S₀)⁰ F))
        (sourcePrimeExponentGenerator_ideal F hζ S₀ e)
    _ = _ := by
      rw [coeIdeal_span_singleton, coe_toPrincipalIdeal, sourcePrimeExponentUnit_val]
      rfl

theorem sourceQuadraticIdealClass_generator (e : E) :
    sourceQuadraticIdealClass F S₀ hζ
        (integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e)
          (sourcePrimeExponentIdeal_ne_bot F S₀ e)) =
      sourceQuadraticLocalClass F S₀ hζ e := by
  change sourceComplementSquareClass F S₀ hζ
    (sourceComplementIdealClass F S₀ hζ (extendedIdealGroup F S₀ _)) = _
  rw [sourcePrimeExponentIdeal_extended F S₀ hζ,
    sourceComplementIdealClass_principal]
  change sourceComplementSquareClass F S₀ hζ
    (sourceComplementClassProjection F S₀ hζ
      (sLocalRingGlobalClassMap F 6 S (sourcePrimeExponentUnit F hζ S₀ e))) = _
  rw [sourceComplementClassProjection_allowed F S₀ hζ
    ⟨_, sourcePrimeExponentUnit_allowed F hζ S₀ e⟩]
  rfl

theorem sourceQuadraticLocalClass_ray_factorization (e : E) :
    sourceQuadraticLocalClass F S₀ hζ e =
      sourceQuadraticRayClassMap F S₀ hζ (sourcePrimeExponentRayClass F S₀ e) := by
  rw [sourcePrimeExponentRayClass, sourceQuadraticRayClassMap_ideal,
    sourcePrimeExponentRayIdeal_coe, sourceQuadraticIdealClass_generator]

theorem sourcePrimeExponentRayClass_eq_localClass (e f : E)
    (h : sourcePrimeExponentRayClass F S₀ e = sourcePrimeExponentRayClass F S₀ f) :
    sourceQuadraticLocalClass F S₀ hζ e = sourceQuadraticLocalClass F S₀ hζ f := by
  rw [sourceQuadraticLocalClass_ray_factorization F S₀ hζ e,
    sourceQuadraticLocalClass_ray_factorization F S₀ hζ f, h]

end
end ArtinMatthews.SourceEulerAssembly
