module

public import ArtinMatthews.QuadraticB3TailScale
public import ArtinMatthews.QuadraticHeckeFiniteEnergy
public import ArtinMatthews.SourcePrimeExponents
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The aggregate tail keeps the common-ideal factor supplied by the divisor estimate. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticB3_weighted_tail_common_bound {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ))
    (C : ℝ) (hC : 0 ≤ C) (g : E) (cols : Finset E) (u : E → ℂ) :
    C * (q g : ℝ) ^ 4 *
        (P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
          K ^ (2 - quadraticB3TailLine δ))) * coeffMass cols u ≤
      C * (q g : ℝ) ^ 4 * M * coeffMass cols u := by
  apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
  exact mul_le_mul_of_nonneg_left
    (quadraticB3_tail_pair_bound hM hP hδ hlower hupper)
    (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) 4))

theorem sourceQuadraticB3_weighted_tail_to_block {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ))
    (C : ℝ) (hC : 0 ≤ C) (g : E) (cols : Finset E) (u : E → ℂ) (α : ℝ) :
    C * (q g : ℝ) ^ 4 *
        (P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
          K ^ (2 - quadraticB3TailLine δ))) * coeffMass cols u ≤
      (C * (q g : ℝ) ^ 4 * (M * P) ^ δ *
        (M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P)) *
          coeffMass cols u := by
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hK0 := (quadraticB3_cutoff_range hM hP hδ hlower hupper).1
  have hrest : M ≤ M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P := by
    have hterm : 0 ≤ Real.sqrt M * K ^ (α - 1 / 2) := by positivity
    have hterm' : 0 ≤ Real.sqrt (M / K) * P := by positivity
    linarith
  have hscale : M ≤ (M * P) ^ δ *
      (M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P) := by
    exact hrest.trans (le_mul_of_one_le_left (hM0.le.trans hrest)
      (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hP) hδ.le))
  refine (sourceQuadraticB3_weighted_tail_common_bound F S₀ hM hP hδ
    hlower hupper C hC g cols u).trans ?_
  apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale
    (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) 4))

end
end ArtinMatthews.SourceEulerAssembly
