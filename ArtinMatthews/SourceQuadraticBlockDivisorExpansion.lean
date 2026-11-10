module

public import ArtinMatthews.SourceQuadraticBlockIdeals
public import ArtinMatthews.QuadraticHeckeCharacterCompactNorm
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The exact finite divisor expansion of the full source B3 ideal sum.
The original character coefficient at every divisor is retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain SIntegerPrincipalization VaryingKummerAnalytic
open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}

def sourceQuadraticBlockProfile (t : ℝ) : ℂ := (sourceQuadraticB2Bump t : ℝ)

theorem sourceQuadraticBlockProfile_tsupport :
    tsupport sourceQuadraticBlockProfile = tsupport sourceQuadraticB2Bump := by
  change closure (Function.support sourceQuadraticBlockProfile) = closure (Function.support sourceQuadraticB2Bump)
  congr 1
  ext t
  simp only [Function.mem_support, sourceQuadraticBlockProfile]
  norm_cast

theorem sourceQuadraticBlockProfile_compact : HasCompactSupport sourceQuadraticBlockProfile := by
  change IsCompact (tsupport sourceQuadraticBlockProfile)
  rw [sourceQuadraticBlockProfile_tsupport]
  exact sourceQuadraticB2Bump_compactSupport

theorem sourceQuadraticBlockProfile_positive :
    tsupport sourceQuadraticBlockProfile ⊆ Set.Ioi 0 := by
  rw [sourceQuadraticBlockProfile_tsupport]
  intro t ht
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (sourceQuadraticB2Bump_tsupport ht).1

theorem sourceQuadraticBlockProfile_smooth : ContDiff ℝ ∞ sourceQuadraticBlockProfile :=
  Complex.ofRealCLM.contDiff.comp sourceQuadraticB2Bump_smooth

def sourceQuadraticBlockModulus (g : E) : Ideal (𝓞 F) :=
  sourceQuadraticBlockBadIdeal F S₀ * sourcePrimeExponentIdeal F S₀ g

theorem sourceQuadraticBlockModulus_ne_bot (g : E) :
    sourceQuadraticBlockModulus F S₀ g ≠ ⊥ := by
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr (principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))
  · exact sourcePrimeExponentIdeal_ne_bot F S₀ g

theorem sourceQuadraticBlock_divisorNorm_pos (g : E) (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g)) :
    0 < (Ideal.absNorm d : ℝ) := by
  have hm := sourceQuadraticBlockModulus_ne_bot F S₀ g
  have hdiv := (HeckeIdealMobius.mem_divisors F hm).mp hd
  have hd0 : d ≠ ⊥ := ne_zero_of_dvd_ne_zero hm hdiv
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd0)

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

/-- Exact finite Möbius expansion of IdealFull, before applying any Poisson formula. -/
theorem sourceQuadraticBlockIdealFull_eq_divisor_sums {M : ℝ} (hM : 0 < M) (g e : E) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g e =
      ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        (moebius d : ℂ)*(sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient d *
          ∑' J : J₀, (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
            sourceQuadraticBlockProfile ((Ideal.absNorm J.val : ℝ)/(M/(Ideal.absNorm d : ℝ))) := by
  have h := quadraticHeckeCharacterCoprimeNorm_reindex_compact F
    (sourceQuadraticRayCharacter F S₀ hζ e) (sourceQuadraticBlockModulus F S₀ g)
    (sourceQuadraticBlockModulus_ne_bot F S₀ g) sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_smooth.continuous hM
  simpa only [sourceQuadraticBlockIdealFull, sourceQuadraticBlockModulus,
    IsCoprime.mul_right_iff, sourceQuadraticBlockProfile] using h

end
end ArtinMatthews.SourceEulerAssembly
