module

public import ArtinMatthews.ReflectionCoefficientGaussCRT
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

/-! The literal global quadratic Gauss factor in directed-pair form.
This is the form needed to combine with the actual finite-F CRT factors;
the cross-prime characters are expanded rather than discarded. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open SIntegerFourier StandardAdelic SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def reflectionPrimeCrossCharacter (P Q : SourceExteriorPrime F S₀) : ℂ :=
  generatorResidueCharacter (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (reflectionPrimeCharacters F hζ S₀ P)
    (Ideal.Quotient.mk _ (sourceAllowedPrimeGenerator F hζ S₀ Q))

def reflectionGaussDirectedPairs (c : ReflectionSquarefreeExponents F S₀) : ℂ :=
  ∏ P : c.val.support, ∏ Q ∈ Finset.univ.erase P,
    reflectionPrimeCrossCharacter F hζ S₀ P.val Q.val ^ 2

def reflectionGaussPrimeProduct (c : ReflectionSquarefreeExponents F S₀) : ℂ :=
  ∏ P : c.val.support,
    residueSourceTau (sourceHilbertSeed F S₀) P.val.val P.val.property
      (sourceAllowedPrimeGenerator F hζ S₀ P.val)
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val)
      (reflectionPrimeCharacters F hζ S₀ P.val ^ 2)

theorem reflectionGammaTwoCRTProduct_eq_directed (c : ReflectionSquarefreeExponents F S₀) :
    reflectionGammaTwoCRTProduct F hζ S₀ c =
      reflectionGaussDirectedPairs F hζ S₀ c * reflectionGaussPrimeProduct F hζ S₀ c := by
  unfold reflectionGammaTwoCRTProduct reflectionGaussDirectedPairs reflectionGaussPrimeProduct
  dsimp only
  congr 1
  apply Finset.prod_congr rfl
  intro P _
  simp only [sourcePrimeCofactor, map_prod, ← Finset.prod_pow, reflectionPrimeCrossCharacter]
  apply Finset.prod_congr rfl
  intro Q _
  exact congrArg (fun x : sourceRing F S₀ =>
    (generatorResidueCharacter (sourceHilbertSeed F S₀) P.val.val P.val.property
      (sourceAllowedPrimeGenerator F hζ S₀ P.val)
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val)
      (reflectionPrimeCharacters F hζ S₀ P.val) (Ideal.Quotient.mk _ x)) ^ 2)
    (pow_one (sourceAllowedPrimeGenerator F hζ S₀ Q.val))

theorem reflectionGammaTwo_eq_directed (c : ReflectionSquarefreeExponents F S₀) :
    reflectionGammaTwo F hζ S₀ c.val =
      (reflectionGaussDirectedPairs F hζ S₀ c * reflectionGaussPrimeProduct F hζ S₀ c) /
        (Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) := by
  rw [reflectionGammaTwo_eq_crt, reflectionGammaTwoCRTProduct_eq_directed]

end
end ArtinMatthews.VaryingKummerAnalytic
