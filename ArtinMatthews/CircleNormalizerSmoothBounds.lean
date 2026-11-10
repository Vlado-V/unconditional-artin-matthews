module

public import ArtinMatthews.CircleNormalizerSmooth
public import ArtinMatthews.CircleDetector
public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleNormalizer
public import ArtinMatthews.CircleNormalizerMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The concrete smooth cutoff satisfies the actual circle-normalizer estimates. -/

noncomputable section
namespace ArtinMatthews

theorem circleSmoothNormalizer_lower (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ F r L : ℕ, 0 < F → 0 < r → F.Coprime r →
      4 * (F * r) ≤ L →
      C * (L : ℝ)^(2-ε) / ((F : ℝ)*(r : ℝ)^ε) ≤
        circleNormalizer (circleModuli F r L) (circleSmoothWeight L) := by
  obtain ⟨C, hC, hbound⟩ := circleNormalizer_lower ε hε hεone
  refine ⟨C, hC, fun F r L hF hr hFr hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  exact hbound F r L hF hr hFr hL (circleSmoothWeight L)
    (fun q _ => circleSmoothWeight_nonneg L q)
    (fun q hq1 hq2 => (circleSmoothWeight_plateau hLpos hq1 hq2).symm.le)

theorem circleSmoothNormalizer_positive {F r L : ℕ} (hF : 0 < F) (hr : 0 < r)
    (hFr : F.Coprime r) (hL : 4 * (F * r) ≤ L) :
    0 < circleNormalizer (circleModuli F r L) (circleSmoothWeight L) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  exact circleNormalizer_positive hF hr hFr hL (circleSmoothWeight L)
    (fun q _ => circleSmoothWeight_nonneg L q)
    (fun q hq1 hq2 => (circleSmoothWeight_plateau hLpos hq1 hq2).symm.le)

theorem circleSmoothWeightMass_le {F r L : ℕ} (hL : 1 ≤ L) :
    circleWeightMass (circleModuli F r L) (circleSmoothWeight L) ≤ 4 * L := by
  simpa only [mul_one] using circleModuli_weightMass_le F r L hL (circleSmoothWeight L)
    1 zero_le_one (fun q _ => circleSmoothWeight_le_one L q)

end ArtinMatthews
