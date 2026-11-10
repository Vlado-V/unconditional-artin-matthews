module

public import ArtinMatthews.SourceQuadraticBlockSquarefreeTail
public import ArtinMatthews.SourceQuadraticLocalClasses
public import ArtinMatthews.SourceQuadraticDivisorTail
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
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The actual divisor-weighted squarefree tail for a same-class column pair. -/
theorem sourceQuadraticSquarefreePairTail_bound (σ : ℝ) (hσ : 2 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M P K : ℝ), 0 < M → 0 < P → 0 < K →
      ∀ (b c g : E), sourceReflectionIsSquarefree b → sourceReflectionIsSquarefree c →
      b ⊓ c = g → sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c →
      (q b : ℝ) ≤ 2 * P → (q c : ℝ) ≤ 2 * P →
      ‖sourceQuadraticBlockSquarefreeTail F S₀ hζ M g ((b - g) + (c - g)) K‖ ≤
        C * (q g : ℝ) ^ 4 * (M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ)) := by
  obtain ⟨A, hA, htail⟩ := sourceQuadraticBlockSquarefreeTail_bound F S₀ hζ
    (u := 2) (σ := σ) (by norm_num) hσ
  obtain ⟨B, hB, hdivisor⟩ := sourceQuadraticB3_divisor_tail_bound F S₀ hζ σ hσ
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro M P K hM hP hK b c g hb hc hg hclass hbP hcP
  calc
    _ ≤ A * ∑ d ∈ VaryingKummerAnalytic.HeckeIdealMobius.divisors F
        (sourceQuadraticBlockModulus F S₀ g),
        ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M ((b - g) + (c - g)) d‖ *
          sourceQuadraticBlockDualScale F S₀ hζ M ((b - g) + (c - g)) d ^ (-σ) *
            K ^ ((2 : ℝ) - σ) := htail M hM g ((b - g) + (c - g)) K hK
    _ ≤ A * (B * (q g : ℝ) ^ 4 *
        (M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ))) :=
      mul_le_mul_of_nonneg_left
        (hdivisor M P K hM hP hK b c g hb hc hg hclass hbP hcP) hA
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
