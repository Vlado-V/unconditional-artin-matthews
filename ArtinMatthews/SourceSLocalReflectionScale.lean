module

public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SLocalLogarithm
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourcePrimeExponentProducts
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

/-! The reflected norm sheet uses the original exterior exponent norms
and the literal reciprocal of the source term scale. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SourceEulerAssembly
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "N" => sourcePrimeExponentNorm K S₀
local notation "b" => sourcePrimeExponentUnit K hζ S₀

theorem sourceSLocalReflectionExponentNorm (e : E) :
    sLocalNorm K S (sWholeDiagonal K S (((b e)⁻¹)^2)) = (N e : ℝ)^(-2 : ℝ) := by
  change fieldSNorm K S (((b e)⁻¹)^2) = _
  rw [map_pow,map_inv,sourcePrimeExponentUnit_fieldSNorm K hζ S₀ e,
    Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_two,inv_pow]

theorem sourceSLocalReflectionActiveExponentNorm
    (f : Finset (SourceExteriorPrime K S₀)) (d : E) :
    sLocalNorm K S
        (sWholeDiagonal K S (((b (sourceReflectionActiveExponents K S₀ f+d))⁻¹)^2)) =
      (((N d : ℝ)^2)*((N (sourceReflectionActiveExponents K S₀ f) : ℝ)^2))⁻¹ := by
  rw [sourceSLocalReflectionExponentNorm K hζ S₀,sourcePrimeExponentNorm_add,Nat.cast_mul]
  rw [Real.rpow_neg (by positivity),Real.rpow_two,mul_pow,
    mul_comm ((N (sourceReflectionActiveExponents K S₀ f) : ℝ)^2)]

theorem sourceSLocalReflectionTermScale_inv (Z : ℝ)
    (f : Finset (SourceExteriorPrime K S₀)) (d : E) :
    sLocalNorm K S
        (sWholeDiagonal K S (((b (sourceReflectionActiveExponents K S₀ f+d))⁻¹)^2)) / Z⁻¹ =
      (sourceReflectionTermScale K S₀ Z f d)⁻¹ := by
  rw [sourceSLocalReflectionActiveExponentNorm K hζ S₀,sourceReflectionTermScale,
    div_inv_eq_mul,inv_div,div_eq_mul_inv,mul_comm]

end
end ArtinMatthews
