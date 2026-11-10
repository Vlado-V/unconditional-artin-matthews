module

public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.SIntegerResidueGauss
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

/-! The cubic angular Gauss identity holds in the literal standard
generator phase. The additive phase is kept throughout the genuine
finite-field Jacobi calculation. -/

namespace ArtinMatthews.AngularLambda

open NumberField IsDedekindDomain
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open VaryingKummerAnalytic
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] {ζ : F}

local instance sourceCubeQuotientField (P : HeightOneSpectrum (𝓞 F)) :
    Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance sourceCubeQuotientFinite (P : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance sourceCubeQuotientFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem sourceAngularGammaTwo_cube (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ StandardAdelic.traceBadPlaces F) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase S₀ P hP a ha) 2 ^ 3 =
      -cyclotomicAngularIdeal hζ P.asIdeal := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  let : (angularPrimeBelow F P).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
  let : P.asIdeal.LiesOver (angularPrimeBelow F P) := Ideal.over_under P.asIdeal
  exact angularPrime_gammaTwo_cube F P.asIdeal (angularPrimeBelow F P)
    (angularPrimeBelow_good F P (prime_not_three_of_not_six F P hsix))
    (residueSourcePhase S₀ P hP a ha) (residueSourcePhase_primitive S₀ P hP a ha hbad)

end

end ArtinMatthews.AngularLambda
