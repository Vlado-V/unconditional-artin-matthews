module

public import ArtinMatthews.ReflectionGaussPrefix
public import ArtinMatthews.SourceFrequencyUnitReduction
public import ArtinMatthews.SourceFiniteGammaUnitCancellation
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

/-! The actual global gamma2 times the literal finite Poisson coefficient
is the finite product of local Gauss, residual-character and stripped
coefficient factors. This keeps the finite sum and all CRT units until
their exact cancellation. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic SIntegerFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourcePrimeStrippedCoefficient (P : SourceExteriorPrime F S₀) (t k J : ℕ) : ℂ :=
  standardLocalCoefficient (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (reflectionPrimeCharacters F hζ S₀ P) t k J

theorem sourcePrimeStrippedCoefficient_zero_zero (P : SourceExteriorPrime F S₀) (J : ℕ) :
    sourcePrimeStrippedCoefficient F hζ S₀ P 0 0 J = 1 := rfl

theorem sourceGammaTwo_finiteF_product (c : ReflectionSquarefreeExponents F S₀)
    (l k r : SourcePrimeExponents F S₀) (u : sourceRing F S₀) (hu : u ≠ 0)
    (T : Finset (SourceExteriorPrime F S₀))
    (hc : c.val.support ⊆ T) (hk : k.support ⊆ T) (hA : (c.val + 3 • l).support ⊆ T) :
    let A := c.val + 3 • l
    reflectionGammaTwo F hζ S₀ c.val * sourceExponentFiniteF F hζ S₀
        (reflectionPrimeCharacters F hζ S₀) k A (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6) =
      ∏ P : T, reflectionNormalizedPrimeGamma F hζ S₀ P.val ^ c.val P.val *
        ((sourceResidualCharacterUnit F hζ S₀ u hu P.val ^ ((k P.val : ℤ) - A P.val) : ℂˣ) : ℂ) *
        sourcePrimeStrippedCoefficient F hζ S₀ P.val (A P.val) (k P.val)
          (sourceElementExponents F S₀ u hu P.val + 6 * r P.val) := by
  let A := c.val + 3 • l
  let D := ∏ P ∈ T, ∏ Q ∈ T, reflectionGaussPairKernel F hζ S₀ c P Q
  let G (P : T) := reflectionNormalizedPrimeGamma F hζ S₀ P.val ^ c.val P.val
  let U (P : T) := sourceExponentCRTUnitFactor F S₀ hζ
    (reflectionPrimeCharacters F hζ S₀) k A r u hu T P
  let W (P : T) : ℂ :=
    ((sourceResidualCharacterUnit F hζ S₀ u hu P.val ^ ((k P.val : ℤ) - A P.val) : ℂˣ) : ℂ)
  let C (P : T) := sourcePrimeStrippedCoefficient F hζ S₀ P.val (A P.val) (k P.val)
    (sourceElementExponents F S₀ u hu P.val + 6 * r P.val)
  have hΓ : reflectionGammaTwo F hζ S₀ c.val = D * ∏ P : T, G P := by
    calc
      _ = D * ∏ P ∈ T, reflectionNormalizedPrimeGamma F hζ S₀ P ^ c.val P :=
        reflectionGammaTwo_eq_prefix F hζ S₀ c T hc
      _ = _ := congrArg (D * ·) (Finset.prod_coe_sort T
        (fun P => reflectionNormalizedPrimeGamma F hζ S₀ P ^ c.val P)).symm
  have hF : sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) k A
      (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6) = ∏ P : T, U P * C P :=
    sourceExponentFiniteF_normalized F S₀ hζ (reflectionPrimeCharacters F hζ S₀) k A r u hu T hk hA
  have hU : D * (∏ P : T, U P) = ∏ P : T, W P :=
    sourceFiniteGammaUnitFactor_cancel F hζ S₀ c l k r u hu T
  change reflectionGammaTwo F hζ S₀ c.val * sourceExponentFiniteF F hζ S₀
    (reflectionPrimeCharacters F hζ S₀) k A (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6) =
      ∏ P : T, G P * W P * C P
  rw [hΓ, hF, Finset.prod_mul_distrib]
  calc
    _ = (∏ P : T, G P) * (D * ∏ P : T, U P) * (∏ P : T, C P) := by ac_rfl
    _ = _ := by rw [hU, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

end
end ArtinMatthews.SourceEulerAssembly
