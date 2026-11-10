module

public import ArtinMatthews.QuadraticHeckeCutoffSupport
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourceReflectionPowerful
public import ArtinMatthews.QuadraticHeckeMaskedCutoff
public import ArtinMatthews.SourcePrimeIdealFactorization
public import ArtinMatthews.SourceReflectionExteriorRows
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Bad" => (Ideal.span {principalizingDenominator (sourceHilbertSeed F S₀)} : Ideal (𝓞 F))

/-- The fixed denominator mask stays on every term for an actual exterior common ideal. -/
theorem sourceQuadraticMainTerm_badIdealCutoff {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M)
    (hχ : ∀ J : Ideal (𝓞 F), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g : E) (hg : sourceReflectionIsSquarefree g) (hgM : IsCoprime (I g) M) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff F H,
      if IsCoprime a Bad then quadraticHeckeHalfCoefficient F ψ a else 0) *
        (∑ e ∈ HeckeIdealMobius.divisors F (I g),
          (UniqueFactorizationMonoid.moebius e : ℂ) * quadraticHeckeHalfCoefficient F ψ e) -
      (∑ h ∈ quadraticHeckeCoprimeCutoff F (I g) H,
        if IsCoprime h Bad then quadraticHeckeHalfCoefficient F ψ h else 0) *
          quadraticHeckeCoprimeDensity F (I g) =
      ∑ b ∈ quadraticHeckeCutoffAnnulus F (I g) H, if IsCoprime b Bad then
        quadraticHeckeCutoffCoefficient F (I g) H b * quadraticHeckeHalfCoefficient F ψ b else 0 :=
  quadraticHeckeMainTerm_maskedCutoffGrouped F ψ hχ (I g) Bad
    ((sourceReflectionExteriorIdeal_squarefree F S₀ g).mpr hg) hgM
    (sourcePrimeExponentIdeal_exterior F S₀ g).2 H

end
end ArtinMatthews.SourceEulerAssembly
