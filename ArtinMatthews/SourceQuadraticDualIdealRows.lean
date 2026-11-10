module

public import ArtinMatthews.SourceQuadraticRadicalRows
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceQuadraticPairBadTriviality
public import ArtinMatthews.SourceQuadraticSmallAmplitude
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

/-! All squarefree ideal rows split into a fixed bad divisor and an
actual exterior row. The original product cutoff is retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

omit [IsTotallyComplex F] in
theorem sourceQuadraticDual_zero_radical :
    sourceQuadraticBlockRadical F S₀ 0 = quadraticHeckeIdealRadical F Bad := by
  simp only [sourceQuadraticBlockRadical, sourcePrimeExponentIdeal_zero, mul_one]

theorem sourceQuadraticDual_bad_row_coefficient (b c g a : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (d : Ideal (𝓞 F)) (hd : d ∣ quadraticHeckeIdealRadical F Bad) :
    (Ψ ((b-g)+(c-g))).allCoefficient (I a * d) = χ a (b-g) * χ a (c-g) := by
  rw [EvenIdealRayCharacter.allCoefficient_mul,
    sourceQuadraticPair_badIdeal_coefficient_one F S₀ hζ b c g hg hclass d
      (hd.trans (quadraticHeckeIdealRadical_dvd F Bad)), mul_one,
    sourceQuadraticSmallPair_coefficient F S₀ hζ b c g hb hc hg a]

theorem sourceQuadraticDual_all_ideal_rows (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (K : ℝ) (H : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff F K,
      (Ψ ((b-g)+(c-g))).allCoefficient a * H a) =
    ∑ a ∈ sourceQuadraticBlockRadicalRows F S₀ 0 K,
      ∑ d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad),
        if (q a : ℝ) * (Ideal.absNorm d : ℝ) ≤ K then
          χ a (b-g) * χ a (c-g) * H (I a * d) else 0 := by
  rw [quadraticHeckeSquarefreeCutoff_split F (quadraticHeckeIdealRadical F Bad)
    (quadraticHeckeIdealRadical_squarefree F Bad) K]
  have hrow := sourceQuadraticBlockRadicalRows_sum F S₀ 0 K
    (fun a => ∑ d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad),
      if (Ideal.absNorm (a*d) : ℝ) ≤ K then
        (Ψ ((b-g)+(c-g))).allCoefficient (a*d) * H (a*d) else 0)
  rw [sourceQuadraticDual_zero_radical F S₀] at hrow
  rw [← hrow]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_mul, Nat.cast_mul, sourcePrimeExponentIdeal_norm]
  split_ifs with h
  · rw [sourceQuadraticDual_bad_row_coefficient F S₀ hζ b c g a hb hc hg hclass d
      ((HeckeIdealMobius.mem_divisors F (quadraticHeckeIdealRadical_ne_bot F Bad)).mp hd)]
  · rfl

end
end ArtinMatthews.SourceEulerAssembly
