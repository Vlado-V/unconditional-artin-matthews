module

public import ArtinMatthews.SourceQuadraticDualSquarefreeSplit
public import ArtinMatthews.QuadraticHeckeCoprimeContourRemainder
public import ArtinMatthews.QuadraticHeckeCutoffSplit
public import ArtinMatthews.QuadraticHeckeSquareMellin
public import ArtinMatthews.SourceQuadraticBlockPoissonExpansion
public import ArtinMatthews.QuadraticHeckeRescaledSquareContour
public import ArtinMatthews.QuadraticHeckeSmallResidue
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

/-! Finite squarefree dual contours at an arbitrary cutoff, with the
complementary tail and every outer divisor coefficient retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set VaryingKummerAnalytic UniqueFactorizationMonoid
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation:max "Q" e:max => (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F
local notation "D" => quadraticHeckeDualProfile A r sourceQuadraticBlockProfile

def sourceQuadraticDualSquarefreeContours (e : E) (X U σ : ℝ) : ℂ :=
  ∑ a ∈ quadraticHeckeSquarefreeCutoff F U, (Ψ e).allCoefficient a *
    (quadraticHeckeCoprimeContourRemainder F (sourceQuadraticConductor F S₀ hζ e)
      (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile)) σ
      (Real.sqrt (Q e/(X*(Ideal.absNorm a : ℝ)))) +
    (dedekindZeta_residue F : ℂ)*(Real.sqrt (Q e/(X*(Ideal.absNorm a : ℝ))) : ℂ)*
      ((1/2 : ℂ)*mellin sourceQuadraticBlockProfile (1/2))*
      quadraticHeckeCoprimeDensity F (sourceQuadraticConductor F S₀ hζ e))

/-- The truncated dual term is a genuine finite squarefree contour sum.
Its inner coprimality modulus is the actual character conductor. -/
theorem sourceQuadraticDualTruncated_eq_contours (e : E) {X σ : ℝ}
    (hX : 0 < X) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (U : ℝ) :
    sourceQuadraticDualTruncated F S₀ hζ e X U =
      sourceQuadraticDualSquarefreeContours F S₀ hζ e X U σ := by
  rw [sourceQuadraticDualTruncated_eq_squarefree F S₀ hζ e hX U]
  have hinner (a : {J : Ideal (𝓞 F) // Squarefree J}) :
      (∑' b : J₀, if IsCoprime b.val (sourceQuadraticConductor F S₀ hζ e) then
        D ((Ideal.absNorm a.val : ℝ)*(Ideal.absNorm b.val : ℝ)^2/(Q e/X)) else 0) =
      quadraticHeckeCoprimeContourRemainder F (sourceQuadraticConductor F S₀ hζ e)
        (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile)) σ
        (Real.sqrt (Q e/(X*(Ideal.absNorm a.val : ℝ)))) +
      (dedekindZeta_residue F : ℂ)*(Real.sqrt (Q e/(X*(Ideal.absNorm a.val : ℝ))) : ℂ)*
        ((1/2 : ℂ)*mellin sourceQuadraticBlockProfile (1/2))*
        quadraticHeckeCoprimeDensity F (sourceQuadraticConductor F S₀ hζ e) := by
    have hna : 0 < (Ideal.absNorm a.val : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr a.property.ne_zero)
    have h := quadraticHeckeCoprimeRescaledDualSquareContour_shift F
      (sourceQuadraticConductor F S₀ hζ e) (sourceQuadraticConductor_ne_bot F S₀ hζ e)
      A r sourceQuadraticBlockProfile sourceQuadraticBlockProfile_compact
      sourceQuadraticBlockProfile_positive sourceQuadraticBlockProfile_smooth hσ₀ hσ₁
      (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e) hX) hna
    simpa only [div_div] using h
  simp_rw [hinner]
  unfold sourceQuadraticDualSquarefreeContours
  exact quadraticHeckeSquarefreeCutoff_tsum F U (fun a => (Ψ e).allCoefficient a *
    (quadraticHeckeCoprimeContourRemainder F (sourceQuadraticConductor F S₀ hζ e)
      (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile)) σ
      (Real.sqrt (Q e/(X*(Ideal.absNorm a : ℝ)))) +
      (dedekindZeta_residue F : ℂ)*(Real.sqrt (Q e/(X*(Ideal.absNorm a : ℝ))) : ℂ)*
        ((1/2 : ℂ)*mellin sourceQuadraticBlockProfile (1/2))*
        quadraticHeckeCoprimeDensity F (sourceQuadraticConductor F S₀ hζ e)))

/-- An arbitrary squarefree cutoff gives an exact finite part plus an explicit tail. -/
theorem sourceQuadraticDual_full_eq_contours_add_tail (e : E) {X σ : ℝ}
    (hX : 0 < X) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (U : ℝ) :
    (∑' J : J₀, sourceQuadraticDualSummand F S₀ hζ e X J) =
      sourceQuadraticDualSquarefreeContours F S₀ hζ e X U σ +
        sourceQuadraticDualSquarefreeTail F S₀ hζ e X U := by
  rw [sourceQuadraticDual_full_eq_truncated_add_tail F S₀ hζ e hX U,
    sourceQuadraticDualTruncated_eq_contours F S₀ hζ e hX hσ₀ hσ₁ U]

/-- The squarefree cutoff may depend on the original finite divisor. -/
def sourceQuadraticDualDivisorContours (M σ : ℝ) (g e : E)
    (U : Ideal (𝓞 F) → ℝ) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    (moebius d : ℂ)*(Ψ e).allCoefficient d *
      ((M/(Ideal.absNorm d : ℝ))/Real.sqrt (Q e) : ℝ) *
      (sourceQuadraticDualSquarefreeContours F S₀ hζ e (M/(Ideal.absNorm d : ℝ)) (U d) σ +
        sourceQuadraticDualSquarefreeTail F S₀ hζ e (M/(Ideal.absNorm d : ℝ)) (U d))

theorem sourceQuadraticBlockNonzeroPoissonSum_eq_dualContours {M σ : ℝ}
    (hM : 0 < M) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (g e : E)
    (U : Ideal (𝓞 F) → ℝ) :
    sourceQuadraticBlockNonzeroPoissonSum F S₀ hζ M g e =
      sourceQuadraticDualDivisorContours F S₀ hζ M σ g e U := by
  unfold sourceQuadraticBlockNonzeroPoissonSum sourceQuadraticDualDivisorContours
  apply Finset.sum_congr rfl
  intro d hd
  have hX : 0 < M/(Ideal.absNorm d : ℝ) :=
    div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd)
  have h := sourceQuadraticDual_full_eq_contours_add_tail F S₀ hζ e hX hσ₀ hσ₁ (U d)
  unfold sourceQuadraticDualSummand at h
  rw [h]

/-- The actual nonzero source IdealFull with a free divisor-dependent cutoff. -/
theorem sourceQuadraticBlockIdealFull_eq_dualContours {M σ : ℝ}
    (hM : 0 < M) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (g e : E)
    (he : sourceReflectionIsSquarefree e) (hne : e ≠ 0) (U : Ideal (𝓞 F) → ℝ) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g e =
      sourceQuadraticDualDivisorContours F S₀ hζ M σ g e U := by
  rw [sourceQuadraticBlockIdealFull_eq_nonzeroPoisson F S₀ hζ hM g e he hne,
    sourceQuadraticBlockNonzeroPoissonSum_eq_dualContours F S₀ hζ hM hσ₀ hσ₁ g e U]

end
end ArtinMatthews.SourceEulerAssembly
