module

public import ArtinMatthews.SourceQuadraticBlockDivisorExpansion
public import ArtinMatthews.QuadraticHeckeDualProfile
public import ArtinMatthews.QuadraticHeckeFieldNormalization
public import ArtinMatthews.SourceQuadraticNormPoisson
public import ArtinMatthews.SourceQuadraticPrincipalNormPoisson
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

/-! Exact source-family Poisson on each term of the finite divisor
expansion. The zero-exponent principal residue is kept separately. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.ProbePhysical
open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "D" => quadraticHeckeDualProfile (quadraticHeckeFieldScale F)
  (InfinitePlace.nrComplexPlaces F) sourceQuadraticBlockProfile

def sourceQuadraticBlockNonzeroPoissonSum (M : ℝ) (g e : E) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    (moebius d : ℂ)*(Ψ e).allCoefficient d *
      ((M/(Ideal.absNorm d : ℝ)) /
        Real.sqrt (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ) : ℝ) *
      ∑' J : J₀, (Ψ e).allCoefficient J.val *
        D ((Ideal.absNorm J.val : ℝ)*(M/(Ideal.absNorm d : ℝ)) /
          (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ))

def sourceQuadraticBlockPrincipalPoissonSum (M : ℝ) (g : E) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    (moebius d : ℂ)*(Ψ 0).allCoefficient d *
      ((dedekindZeta_residue F : ℂ)*(M/(Ideal.absNorm d : ℝ) : ℝ)*
          mellin sourceQuadraticBlockProfile 1 +
        (M/(Ideal.absNorm d : ℝ) : ℝ)*
          ∑' J : J₀, (Ψ 0).allCoefficient J.val *
            D ((M/(Ideal.absNorm d : ℝ))*(Ideal.absNorm J.val : ℝ)))

/-- The nonprincipal source character is transformed at each exact rescaled norm. -/
theorem sourceQuadraticBlockIdealFull_eq_nonzeroPoisson {M : ℝ} (hM : 0 < M)
    (g e : E) (he : sourceReflectionIsSquarefree e) (hne : e ≠ 0) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g e =
      sourceQuadraticBlockNonzeroPoissonSum F S₀ hζ M g e := by
  rw [sourceQuadraticBlockIdealFull_eq_divisor_sums F S₀ hζ hM g e]
  unfold sourceQuadraticBlockNonzeroPoissonSum
  apply Finset.sum_congr rfl
  intro d hd
  have hX : 0 < M/(Ideal.absNorm d : ℝ) :=
    div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd)
  have h := sourceQuadraticRayCharacter_normPoisson F S₀ hζ e he hne
    sourceQuadraticBlockProfile sourceQuadraticBlockProfile_compact
    sourceQuadraticBlockProfile_positive sourceQuadraticBlockProfile_smooth hX
  rw [h]
  ring

/-- The principal source character contributes its exact residue at every divisor scale. -/
theorem sourceQuadraticBlockIdealFull_eq_principalPoisson {M : ℝ} (hM : 0 < M) (g : E) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g 0 =
      sourceQuadraticBlockPrincipalPoissonSum F S₀ hζ M g := by
  rw [sourceQuadraticBlockIdealFull_eq_divisor_sums F S₀ hζ hM g 0]
  unfold sourceQuadraticBlockPrincipalPoissonSum
  apply Finset.sum_congr rfl
  intro d hd
  have hX : 0 < M/(Ideal.absNorm d : ℝ) :=
    div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd)
  rw [sourceQuadraticRayCharacter_zero_normPoisson F S₀ hζ sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hX]

/-- Both cases of the actual source family, with the principal branch explicit. -/
theorem sourceQuadraticBlockIdealFull_eq_poisson {M : ℝ} (hM : 0 < M)
    (g e : E) (he : sourceReflectionIsSquarefree e) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g e =
      if e = 0 then sourceQuadraticBlockPrincipalPoissonSum F S₀ hζ M g else
        sourceQuadraticBlockNonzeroPoissonSum F S₀ hζ M g e := by
  by_cases hz : e = 0
  · subst e
    rw [ite_eq_left rfl]
    exact sourceQuadraticBlockIdealFull_eq_principalPoisson F S₀ hζ hM g
  · rw [ite_eq_right hz]
    exact sourceQuadraticBlockIdealFull_eq_nonzeroPoisson F S₀ hζ hM g e he hz

end
end ArtinMatthews.SourceEulerAssembly
