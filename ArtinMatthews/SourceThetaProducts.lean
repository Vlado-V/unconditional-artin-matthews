module

public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourcePrimeExponentProducts
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The true source Theta coefficient is multiplicative in its actual
ideal exponents, from the angular, Gauss-Hecke and target characters. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators AngularLambda QuadraticWeil
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

theorem reflectionThetaValue_add (e f : SourcePrimeExponents F S₀) :
    reflectionThetaValue F hζ S₀ hS η (e + f) =
      reflectionThetaValue F hζ S₀ hS η e * reflectionThetaValue F hζ S₀ hS η f := by
  have hU : integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ (e + f))
        (sourcePrimeExponentIdeal_ne_bot F S₀ (e + f)) =
      integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ e) (sourcePrimeExponentIdeal_ne_bot F S₀ e) *
        integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ f) (sourcePrimeExponentIdeal_ne_bot F S₀ f) := by
    apply Units.ext
    change (sourcePrimeExponentIdeal F S₀ (e + f) : FractionalIdeal (𝓞 F)⁰ F) =
      (sourcePrimeExponentIdeal F S₀ e : FractionalIdeal (𝓞 F)⁰ F) *
        (sourcePrimeExponentIdeal F S₀ f : FractionalIdeal (𝓞 F)⁰ F)
    rw [sourcePrimeExponentIdeal_add, FractionalIdeal.coeIdeal_mul]
  dsimp only [reflectionThetaValue]
  rw [hU, map_mul, Units.val_mul, sourcePrimeExponentIdeal_add,
    map_mul, η.allCoefficient_mul]
  simp only [star_mul]
  ring

theorem reflectionThetaValue_zero : reflectionThetaValue F hζ S₀ hS η 0 = 1 := by
  have hU : integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ 0)
      (sourcePrimeExponentIdeal_ne_bot F S₀ 0) = 1 := by
    apply Units.ext
    change (sourcePrimeExponentIdeal F S₀ 0 : FractionalIdeal (𝓞 F)⁰ F) = 1
    rw [sourcePrimeExponentIdeal_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top]
  dsimp only [reflectionThetaValue]
  rw [hU]
  simp only [sourcePrimeExponentIdeal_zero, map_one, Units.val_one, star_one,
    η.allCoefficient_one, mul_one]

theorem reflectionThetaValue_nsmul (e : SourcePrimeExponents F S₀) (k : ℕ) :
    reflectionThetaValue F hζ S₀ hS η (k • e) = reflectionThetaValue F hζ S₀ hS η e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, reflectionThetaValue_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, reflectionThetaValue_add, ih, pow_succ]

theorem reflectionThetaValue_single (P : SourceExteriorPrime F S₀) (n : ℕ) :
    reflectionThetaValue F hζ S₀ hS η (Finsupp.single P n) =
      reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) ^ n := by
  rw [← Finsupp.smul_single_one P n, reflectionThetaValue_nsmul]

theorem reflectionThetaValue_prod (e : SourcePrimeExponents F S₀) :
    reflectionThetaValue F hζ S₀ hS η e =
      e.prod (fun P n => reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) ^ n) := by
  refine e.induction ?_ ?_
  · rw [reflectionThetaValue_zero, Finsupp.prod_zero_index]
  · intro P n f _ _ ih
    rw [reflectionThetaValue_add, ih, reflectionThetaValue_single,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    congr 1
    exact (Finsupp.prod_single_index
      (h := fun Q k => reflectionThetaValue F hζ S₀ hS η (Finsupp.single Q 1) ^ k)
      (a := P) (b := n) (pow_zero _)).symm

end
end ArtinMatthews.VaryingKummerAnalytic
