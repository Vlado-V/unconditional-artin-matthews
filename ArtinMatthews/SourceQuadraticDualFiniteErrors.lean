module

public import ArtinMatthews.SourceQuadraticDualSquarefreeContour
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The finite contour error, its explicit residue, and the complementary
squarefree tail of the literal Full dual expression. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Q" e:max => (Ideal.absNorm (C e) : ℝ)
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

def sourceQuadraticDualSquarefreeError (e : E) (X K σ : ℝ) : ℂ :=
  ∑ a ∈ quadraticHeckeSquarefreeCutoff F K, (Ψ e).allCoefficient a *
    quadraticHeckeCoprimeContourRemainder F (C e)
      (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile)) σ
      (Real.sqrt (Q e / (X * (Ideal.absNorm a : ℝ))))

def sourceQuadraticDualSquarefreeResidue (e : E) (X K : ℝ) : ℂ :=
  ∑ a ∈ quadraticHeckeSquarefreeCutoff F K, (Ψ e).allCoefficient a *
    ((dedekindZeta_residue F : ℂ) * (Real.sqrt (Q e / (X * (Ideal.absNorm a : ℝ))) : ℂ) *
      ((1 / 2 : ℂ) * mellin sourceQuadraticBlockProfile (1 / 2)) *
      quadraticHeckeCoprimeDensity F (C e))

theorem sourceQuadraticDualSquarefreeContours_split (e : E) (X K σ : ℝ) :
    sourceQuadraticDualSquarefreeContours F S₀ hζ e X K σ =
      sourceQuadraticDualSquarefreeError F S₀ hζ e X K σ +
        sourceQuadraticDualSquarefreeResidue F S₀ hζ e X K := by
  simp only [sourceQuadraticDualSquarefreeContours, sourceQuadraticDualSquarefreeError,
    sourceQuadraticDualSquarefreeResidue, mul_add, Finset.sum_add_distrib]

theorem sourceQuadraticDualSquarefreeError_line_independent (e : E) {X σ τ : ℝ}
    (hX : 0 < X) (hσ : 0 < σ) (hσ₁ : σ < 1) (hτ : 0 < τ) (hτ₁ : τ < 1) (K : ℝ) :
    sourceQuadraticDualSquarefreeError F S₀ hζ e X K σ =
      sourceQuadraticDualSquarefreeError F S₀ hζ e X K τ := by
  apply add_right_cancel (b := sourceQuadraticDualSquarefreeResidue F S₀ hζ e X K)
  rw [← sourceQuadraticDualSquarefreeContours_split,
    ← sourceQuadraticDualSquarefreeContours_split,
    ← sourceQuadraticDualTruncated_eq_contours F S₀ hζ e hX hσ hσ₁ K,
    ← sourceQuadraticDualTruncated_eq_contours F S₀ hζ e hX hτ hτ₁ K]

def sourceQuadraticDualDivisorError (M K σ : ℝ) (g e : E) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    (moebius d : ℂ) * (Ψ e).allCoefficient d *
      ((M / (Ideal.absNorm d : ℝ)) / Real.sqrt (Q e) : ℝ) *
      sourceQuadraticDualSquarefreeError F S₀ hζ e (M / (Ideal.absNorm d : ℝ)) K σ

def sourceQuadraticDualDivisorResidue (M K : ℝ) (g e : E) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    (moebius d : ℂ) * (Ψ e).allCoefficient d *
      ((M / (Ideal.absNorm d : ℝ)) / Real.sqrt (Q e) : ℝ) *
      sourceQuadraticDualSquarefreeResidue F S₀ hζ e (M / (Ideal.absNorm d : ℝ)) K

def sourceQuadraticDualDivisorTail (M K : ℝ) (g e : E) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    (moebius d : ℂ) * (Ψ e).allCoefficient d *
      ((M / (Ideal.absNorm d : ℝ)) / Real.sqrt (Q e) : ℝ) *
      sourceQuadraticDualSquarefreeTail F S₀ hζ e (M / (Ideal.absNorm d : ℝ)) K

theorem sourceQuadraticDualDivisorContours_split (M K σ : ℝ) (g e : E) :
    sourceQuadraticDualDivisorContours F S₀ hζ M σ g e (fun _ => K) =
      sourceQuadraticDualDivisorError F S₀ hζ M K σ g e +
        sourceQuadraticDualDivisorResidue F S₀ hζ M K g e +
        sourceQuadraticDualDivisorTail F S₀ hζ M K g e := by
  simp only [sourceQuadraticDualDivisorContours, sourceQuadraticDualDivisorError,
    sourceQuadraticDualDivisorResidue, sourceQuadraticDualDivisorTail,
    sourceQuadraticDualSquarefreeContours_split, mul_add, Finset.sum_add_distrib]

theorem sourceQuadraticBlockIdealFull_eq_error_residue_tail {M σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσ₁ : σ < 1) (K : ℝ) (g e : E)
    (he : sourceReflectionIsSquarefree e) (hne : e ≠ 0) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g e =
      sourceQuadraticDualDivisorError F S₀ hζ M K σ g e +
        sourceQuadraticDualDivisorResidue F S₀ hζ M K g e +
        sourceQuadraticDualDivisorTail F S₀ hζ M K g e := by
  rw [sourceQuadraticBlockIdealFull_eq_dualContours F S₀ hζ hM hσ hσ₁ g e he hne
    (fun _ => K), sourceQuadraticDualDivisorContours_split]

end
end ArtinMatthews.SourceEulerAssembly
