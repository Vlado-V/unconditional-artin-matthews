module

public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticDualContourIntegral
public import ArtinMatthews.SourceQuadraticDualIntegrand
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
open NumberField IsDedekindDomain MeasureTheory Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

def sourceQuadraticDualErrorIntegrand (e : E) (X K σ t : ℝ) : ℂ :=
  ∑ a ∈ quadraticHeckeSquarefreeCutoff F K, (Ψ e).allCoefficient a *
    (quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ t *
      (Real.sqrt ((Ideal.absNorm (C e) : ℝ) / (X * (Ideal.absNorm a : ℝ))) : ℂ) ^
        quadraticPoissonLine σ t * quadraticSmallEuler F (C e) (quadraticPoissonLine σ t))

theorem sourceQuadraticDualErrorIntegrand_integrable (e : E) {X σ : ℝ}
    (hX : 0 < X) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) (K : ℝ) :
    Integrable (sourceQuadraticDualErrorIntegrand F S₀ hζ e X K σ) := by
  apply integrable_finsetSum
  intro a ha
  have ha0 : 0 < (Ideal.absNorm a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      ((mem_quadraticHeckeSquarefreeCutoff F).mp ha).1.ne_zero)
  exact (quadraticDualContourIntegrand_integrable F (C e) A r sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hσ hσtop hσone
    (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e)
      (mul_pos hX ha0)))).const_mul _

theorem sourceQuadraticDualSquarefreeError_eq_integral (e : E) {X σ : ℝ}
    (hX : 0 < X) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) (K : ℝ) :
    sourceQuadraticDualSquarefreeError F S₀ hζ e X K σ =
      ∫ t : ℝ, sourceQuadraticDualErrorIntegrand F S₀ hζ e X K σ t := by
  unfold sourceQuadraticDualSquarefreeError sourceQuadraticDualErrorIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    have ha0 : 0 < (Ideal.absNorm a : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        ((mem_quadraticHeckeSquarefreeCutoff F).mp ha).1.ne_zero)
    rw [integral_const_mul, quadraticDualContourRemainder_eq_integral F (C e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) A r sourceQuadraticBlockProfile
      sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
      sourceQuadraticBlockProfile_smooth hσ hσtop hσone
      (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e)
        (mul_pos hX ha0)))]
  · intro a ha
    have ha0 : 0 < (Ideal.absNorm a : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        ((mem_quadraticHeckeSquarefreeCutoff F).mp ha).1.ne_zero)
    exact (quadraticDualContourIntegrand_integrable F (C e) A r sourceQuadraticBlockProfile
      sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
      sourceQuadraticBlockProfile_smooth hσ hσtop hσone
      (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e)
        (mul_pos hX ha0)))).const_mul _

def sourceQuadraticDualErrorBlock (M K σ : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 * sourceQuadraticDualDivisorError F S₀ hζ M K σ g
      ((p.1 - g) + (p.2 - g))

def sourceQuadraticDualBlockIntegrand (M K σ : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E) (t : ℝ) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 *
      ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        (UniqueFactorizationMonoid.moebius d : ℂ) * (Ψ ((p.1-g)+(p.2-g))).allCoefficient d *
        ((M / (Ideal.absNorm d : ℝ)) /
          Real.sqrt (Ideal.absNorm (C ((p.1-g)+(p.2-g)))) : ℝ) *
        sourceQuadraticDualErrorIntegrand F S₀ hζ ((p.1-g)+(p.2-g))
          (M / (Ideal.absNorm d : ℝ)) K σ t

theorem sourceQuadraticDualBlockIntegrand_integrable {M σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1)
    (K : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) :
    Integrable (sourceQuadraticDualBlockIntegrand F S₀ hζ M K σ cols u g) := by
  apply integrable_finsetSum
  intro p _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro d hd
  exact (sourceQuadraticDualErrorIntegrand_integrable F S₀ hζ _
    (div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd))
    hσ hσtop hσone K).const_mul _

theorem sourceQuadraticDualErrorBlock_eq_integral {M σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1)
    (K : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticDualErrorBlock F S₀ hζ M K σ cols u g =
      ∫ t : ℝ, sourceQuadraticDualBlockIntegrand F S₀ hζ M K σ cols u g t := by
  unfold sourceQuadraticDualErrorBlock sourceQuadraticDualBlockIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_const_mul]
    unfold sourceQuadraticDualDivisorError
    rw [integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_const_mul, sourceQuadraticDualSquarefreeError_eq_integral F S₀ hζ _
        (div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd)) hσ hσtop hσone K]
    · intro d hd
      exact (sourceQuadraticDualErrorIntegrand_integrable F S₀ hζ _
        (div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd))
        hσ hσtop hσone K).const_mul _
  · intro p _
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro d hd
    exact (sourceQuadraticDualErrorIntegrand_integrable F S₀ hζ _
      (div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd))
      hσ hσtop hσone K).const_mul _

end
end ArtinMatthews.SourceEulerAssembly
