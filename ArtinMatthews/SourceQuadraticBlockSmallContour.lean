module

public import ArtinMatthews.SourceQuadraticBlockDivisorExpansion
public import ArtinMatthews.QuadraticHeckeCoprimeContourRemainder
public import ArtinMatthews.QuadraticHeckeSquareMellin
public import ArtinMatthews.QuadraticHeckeRescaledSquareContour
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

/-! The actual small-squarepart term, with its original source weight,
has a positive-line contour decomposition at the exact square-root scale. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "SF" => {J : Ideal (𝓞 F) // Squarefree J}

def sourceQuadraticBlockSquareModulus (g e : E) : Ideal (𝓞 F) :=
  sourceQuadraticBlockModulus F S₀ g * sourceQuadraticConductor F S₀ hζ e

omit [IsTotallyComplex F] in
theorem sourceQuadraticBlockSquareModulus_ne_bot (g e : E) :
    sourceQuadraticBlockSquareModulus F S₀ hζ g e ≠ ⊥ :=
  mul_ne_zero (sourceQuadraticBlockModulus_ne_bot F S₀ g)
    (sourceQuadraticConductor_ne_bot F S₀ hζ e)

theorem sourceQuadraticBlockIdealSmall_eq_contours {M K σ : ℝ}
    (hM : 0 < M) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (g e : E) :
    sourceQuadraticBlockIdealSmall F S₀ hζ M K g e =
      ∑' a : SF, if IsCoprime a.val (sourceQuadraticBlockBadIdeal F S₀) ∧
          IsCoprime a.val (sourcePrimeExponentIdeal F S₀ g) ∧ (Ideal.absNorm a.val : ℝ) ≤ K then
        (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient a.val *
          (quadraticHeckeCoprimeContourRemainder F
            (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
            (quadraticHeckeSquareMellin (mellin sourceQuadraticBlockProfile)) σ
            (Real.sqrt (M / (Ideal.absNorm a.val : ℝ))) +
          (dedekindZeta_residue F : ℂ) * (Real.sqrt (M / (Ideal.absNorm a.val : ℝ)) : ℂ) *
            ((1/2 : ℂ) * mellin sourceQuadraticBlockProfile (1/2)) *
            quadraticHeckeCoprimeDensity F (sourceQuadraticBlockSquareModulus F S₀ hζ g e))
        else 0 := by
  rw [sourceQuadraticBlockIdealSmall_eq_squarefree F S₀ hζ hM g e]
  apply tsum_congr
  intro a
  split_ifs with ha
  · congr 1
    have hna : 0 < (Ideal.absNorm a.val : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr a.property.ne_zero)
    have h := quadraticHeckeCoprimeRescaledSquareContour_shift F
      (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
      (sourceQuadraticBlockSquareModulus_ne_bot F S₀ hζ g e)
      sourceQuadraticBlockProfile sourceQuadraticBlockProfile_compact
      sourceQuadraticBlockProfile_positive sourceQuadraticBlockProfile_smooth
      hσ₀ hσ₁ hM hna
    simpa only [sourceQuadraticBlockSquareModulus, sourceQuadraticBlockModulus,
      IsCoprime.mul_right_iff, and_assoc, sourceQuadraticBlockProfile] using h
  · rfl

end
end ArtinMatthews.SourceEulerAssembly
