module

public import ArtinMatthews.SourcePrimeExponentWeights
public import ArtinMatthews.SourceGaussCharacter
public import ArtinMatthews.ReflectionGaussianWeight
public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import ArtinMatthews.PrincipalAngularCorrection
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source02a coefficient row, using fixed proved allowed
prime generators and their finite products. The squarefree Gauss factor
is the actual global finite sum; its CRT cross factors are not discarded.
Absolute convergence and the reflected moment are separate obligations. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SIntegerQuotient StandardAdelic AngularLambda QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def reflectionPrimeCharacters (P : SourceExteriorPrime F S₀) :
    MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ :=
  cyclotomicAngularResidueCharacter hζ P.val
    (source_exterior_six_not_mem F S₀ P.val P.property)

def reflectionExponentResidueValue (e : SourcePrimeExponents F S₀) (m : sourceRing F S₀) : ℂ :=
  sourcePrimeExponentWeight F hζ S₀ (reflectionPrimeCharacters F hζ S₀) e m

theorem reflectionExponentResidueValue_norm_le_one (e : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) : ‖reflectionExponentResidueValue F hζ S₀ e m‖ ≤ 1 :=
  sourcePrimeExponentWeight_norm_le_one F hζ S₀ _ e m

/-- The global normalized Gauss sum. Squaring the full residue character
preserves the source's directed CRT factors. -/
def reflectionGammaTwo (e : SourcePrimeExponents F S₀) : ℂ :=
  let A := sourcePrimeExponentGenerator F hζ S₀ e
  let hA := sourcePrimeExponentGenerator_ne_zero F hζ S₀ e
  (∑' x : (sourceRing F S₀) ⧸ Ideal.span {A},
    (reflectionExponentResidueValue F hζ S₀ e (Quotient.out x)) ^ 2 *
      sIntegerQuotientPhase F (sourceHilbertSet F S₀) A hA x) /
        (Real.sqrt (sourcePrimeExponentNorm F S₀ e : ℝ) : ℂ)

variable [IsTotallyComplex F]
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

def reflectionThetaValue (e : SourcePrimeExponents F S₀) : ℂ :=
  let I := sourcePrimeExponentIdeal F S₀ e
  star (cyclotomicAngularIdeal hζ I) *
    star ((sourceGaussHeckeCharacter F hζ S₀ hS).idealHom
      (integralIdealFractionalUnit I (sourcePrimeExponentIdeal_ne_bot F S₀ e)) : ℂ) *
    η.allCoefficient I

theorem reflectionThetaValue_norm_le_one (e : SourcePrimeExponents F S₀) :
    ‖reflectionThetaValue F hζ S₀ hS η e‖ ≤ 1 := by
  unfold reflectionThetaValue
  rw [norm_mul, norm_mul, norm_star, norm_star,
    EvenIdealRayCharacter.idealHom_norm, mul_one]
  simpa only [one_mul] using mul_le_mul (cyclotomicAngularIdeal_norm_le_one hζ _)
    (η.allCoefficient_norm_le_one _) (norm_nonneg _) zero_le_one

def ReflectionSquarefreeExponents :=
  {e : SourcePrimeExponents F S₀ // ∀ P, e P ≤ 1}

/-- A=c n^3 is literal exponent addition. No coprimality of c and n is imposed. -/
def reflectionCoefficientTerm (c : ReflectionSquarefreeExponents F S₀)
    (n : SourcePrimeExponents F S₀) (m : sourceRing F S₀) (Z : ℝ) : ℂ :=
  let A := c.val + 3 • n
  reflectionGammaTwo F hζ S₀ c.val /
      ((Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) *
        (sourcePrimeExponentNorm F S₀ n : ℂ)) *
    reflectionThetaValue F hζ S₀ hS η A * reflectionExponentResidueValue F hζ S₀ A m *
      (reflectionGaussian ((sourcePrimeExponentNorm F S₀ A : ℝ) / Z) : ℂ)

def reflectionCoefficientRow (m : sourceRing F S₀) (Z : ℝ) : ℂ :=
  ∑' c : ReflectionSquarefreeExponents F S₀, ∑' n : SourcePrimeExponents F S₀,
    reflectionCoefficientTerm F hζ S₀ hS η c n m Z

end
end ArtinMatthews.VaryingKummerAnalytic
