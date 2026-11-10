module

public import ArtinMatthews.ReflectionGaussPrefix
public import ArtinMatthews.SIntegerSexticCrossCancellation
public import ArtinMatthews.SourceFinitePairProduct
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

/-! The actual allowed-generator cross units have sixth power one and
satisfy the proved reciprocity law. Hence the combined finite-F/gamma2
directed factors cancel, pair by pair, on every finite prime set. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open SIntegerPrincipalization SIntegerQuotient SIntegerTameSymbol SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourcePrimeCrossUnit (P Q : SourceExteriorPrime F S₀) (h : P ≠ Q) : ℂˣ :=
  sourceCrossUnit F hζ S₀ P.val Q.val (fun he => h (Subtype.ext he)) P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator F hζ S₀ Q)
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ Q)

theorem sourcePrimeCrossUnit_val (P Q : SourceExteriorPrime F S₀) (h : P ≠ Q) :
    (sourcePrimeCrossUnit F hζ S₀ P Q h : ℂ) = reflectionPrimeCrossCharacter F hζ S₀ P Q := rfl

theorem sourcePrimeCrossUnit_pow_six (P Q : SourceExteriorPrime F S₀) (h : P ≠ Q) :
    sourcePrimeCrossUnit F hζ S₀ P Q h ^ 6 = 1 :=
  sourceCrossUnit_pow_six F hζ S₀ P.val Q.val _ P.property _ _ _ _

theorem sourcePrimeCrossUnit_symm (P Q : SourceExteriorPrime F S₀) (h : P ≠ Q) :
    sourcePrimeCrossUnit F hζ S₀ P Q h = sourcePrimeCrossUnit F hζ S₀ Q P h.symm :=
  sourceCrossUnit_reciprocity F hζ S₀ P.val Q.val _ P.property Q.property _ _ _ _
    (sourceAllowedPrimeUnit_allowed F hζ S₀ P) (sourceAllowedPrimeUnit_allowed F hζ S₀ Q)

def sourcePrimeCrossDiagonalUnit (P Q : SourceExteriorPrime F S₀) : ℂˣ :=
  if h : P = Q then 1 else sourcePrimeCrossUnit F hζ S₀ P Q h

theorem sourcePrimeCrossDiagonalUnit_diag (P : SourceExteriorPrime F S₀) :
    sourcePrimeCrossDiagonalUnit F hζ S₀ P P = 1 := by
  rw [sourcePrimeCrossDiagonalUnit, dite_eq_left rfl]

theorem sourcePrimeCrossDiagonalUnit_pow_six (P Q : SourceExteriorPrime F S₀) :
    sourcePrimeCrossDiagonalUnit F hζ S₀ P Q ^ 6 = 1 := by
  unfold sourcePrimeCrossDiagonalUnit
  split_ifs with h
  · exact one_pow _
  · exact sourcePrimeCrossUnit_pow_six F hζ S₀ P Q h

theorem sourcePrimeCrossDiagonalUnit_symm (P Q : SourceExteriorPrime F S₀) :
    sourcePrimeCrossDiagonalUnit F hζ S₀ P Q = sourcePrimeCrossDiagonalUnit F hζ S₀ Q P := by
  by_cases h : P = Q
  · subst Q
    rfl
  · rw [sourcePrimeCrossDiagonalUnit, dite_eq_right h,
      sourcePrimeCrossDiagonalUnit, dite_eq_right (Ne.symm h)]
    exact sourcePrimeCrossUnit_symm F hζ S₀ P Q h

theorem reflectionGaussPairKernel_unit (c : ReflectionSquarefreeExponents F S₀)
    (P Q : SourceExteriorPrime F S₀) :
    reflectionGaussPairKernel F hζ S₀ c P Q =
      ((sourcePrimeCrossDiagonalUnit F hζ S₀ P Q ^ (2 * c.val P * c.val Q) : ℂˣ) : ℂ) := by
  by_cases h : P = Q
  · subst Q
    rw [reflectionGaussPairKernel, ite_eq_left rfl, sourcePrimeCrossDiagonalUnit_diag,
      one_pow, Units.val_one]
  · rw [reflectionGaussPairKernel, ite_eq_right h,
      sourcePrimeCrossDiagonalUnit, dite_eq_right h, Units.val_pow_eq_pow_val,
      sourcePrimeCrossUnit_val]

def sourceCombinedCrossUnit (e l k : SourcePrimeExponents F S₀)
    (P Q : SourceExteriorPrime F S₀) : ℂˣ :=
  sourcePrimeCrossDiagonalUnit F hζ S₀ P Q ^
    (((e P : ℤ) + 3 * l P) * k Q + ((e P : ℤ) + 3 * l P - k P) * ((e Q : ℤ) + 3 * l Q) +
      2 * (e P : ℤ) * e Q)

theorem sourceCombinedCrossUnit_diag (e l k : SourcePrimeExponents F S₀)
    (P : SourceExteriorPrime F S₀) : sourceCombinedCrossUnit F hζ S₀ e l k P P = 1 := by
  rw [sourceCombinedCrossUnit, sourcePrimeCrossDiagonalUnit_diag, one_zpow]

theorem sourceCombinedCrossUnit_pair (e l k : SourcePrimeExponents F S₀)
    (P Q : SourceExteriorPrime F S₀) :
    sourceCombinedCrossUnit F hζ S₀ e l k P Q * sourceCombinedCrossUnit F hζ S₀ e l k Q P = 1 := by
  unfold sourceCombinedCrossUnit
  rw [← sourcePrimeCrossDiagonalUnit_symm F hζ S₀ P Q, ← zpow_add]
  have he :
      ((e P : ℤ) + 3 * l P) * k Q + ((e P : ℤ) + 3 * l P - k P) * ((e Q : ℤ) + 3 * l Q) +
          2 * (e P : ℤ) * e Q +
        (((e Q : ℤ) + 3 * l Q) * k P + ((e Q : ℤ) + 3 * l Q - k Q) * ((e P : ℤ) + 3 * l P) +
          2 * (e Q : ℤ) * e P) =
      6 * ((e P : ℤ) * e Q + (e P : ℤ) * l Q + (l P : ℤ) * e Q + 3 * (l P : ℤ) * l Q) := by ring
  have hz : sourcePrimeCrossDiagonalUnit F hζ S₀ P Q ^ (6 : ℤ) = 1 := by
    exact (zpow_natCast (sourcePrimeCrossDiagonalUnit F hζ S₀ P Q) 6).trans
      (sourcePrimeCrossDiagonalUnit_pow_six F hζ S₀ P Q)
  rw [he, zpow_mul, hz, one_zpow]

theorem sourceCombinedCrossUnit_finite (e l k : SourcePrimeExponents F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) :
    (∏ P ∈ T, ∏ Q ∈ T, sourceCombinedCrossUnit F hζ S₀ e l k P Q) = 1 := by
  apply sourceFiniteDirectedPairs_cancel T
  · intro P _
    exact sourceCombinedCrossUnit_diag F hζ S₀ e l k P
  · intro P _ Q _ _
    exact sourceCombinedCrossUnit_pair F hζ S₀ e l k P Q

end
end ArtinMatthews.SourceEulerAssembly
