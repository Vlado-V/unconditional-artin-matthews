module

public import ArtinMatthews.SourceGammaFiniteFProduct
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

/-! The actual source local summand, with its four prime exponents,
literal gamma2, and all positive-modulus masks. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

abbrev SourceLocalChoice := Fin 2 × ℕ × ℕ × ℕ

def sourceLocalEulerTerm (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ)
    (P : SourceExteriorPrime F S₀) (a : SourceLocalChoice) : ℂ :=
  let e := a.1.val
  let l := a.2.1
  let k := a.2.2.1
  let m := a.2.2.2
  let t := e + 3 * l
  let Q : ℂ := Ideal.absNorm P.val.asIdeal
  reflectionNormalizedPrimeGamma F hζ S₀ P ^ e *
    ((sourceResidualCharacterUnit F hζ S₀ u hu P ^ ((k : ℤ) - t) : ℂˣ) : ℂ) *
    sourcePrimeStrippedCoefficient F hζ S₀ P t k (sourceElementExponents F S₀ u hu P + 6 * m) *
    reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) ^ t *
    (Q ^ (-(1 / 2 : ℂ) - ξ)) ^ e *
    (Q ^ (-1 - 3 * ξ)) ^ l *
    (Q ^ (-w)) ^ k *
    (Q ^ (-(6 : ℂ) * z)) ^ m

theorem sourceLocalEulerTerm_zero (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ)
    (P : SourceExteriorPrime F S₀) : sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P 0 = 1 := by
  simp only [sourceLocalEulerTerm, Prod.fst_zero, Prod.snd_zero, Fin.val_zero, mul_zero, add_zero,
    Nat.cast_zero, sub_zero, zpow_zero, Units.val_one, pow_zero,
    sourcePrimeStrippedCoefficient_zero_zero, mul_one]

def sourceLocalEulerFactor (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ)
    (P : SourceExteriorPrime F S₀) : ℂ :=
  ∑' a : SourceLocalChoice, sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P a

end
end ArtinMatthews.SourceEulerAssembly
