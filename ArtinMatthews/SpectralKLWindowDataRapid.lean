module

public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralKLCompactRapid
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem spectralKLWindowData_rapid (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
      ‖spectralKLWindowData h g t‖ ≤ C := by
  obtain ⟨K, hK, hk⟩ := spectralKLCompactOrderTransform_strip_rapid g hg hc hp (N + 1)
  refine ⟨H * K, mul_nonneg hH hK, ?_⟩
  intro t
  have hκ := hk 0 t (by norm_num)
  simp only [Complex.ofReal_zero, neg_zero, zero_add] at hκ
  rw [spectralKLWindowData, norm_mul]
  calc
    _ ≤ (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
        ((H * (1 + t ^ 2)) * ‖spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I)‖) := by
      gcongr
      exact hh t
    _ = H * ((1 + t ^ 2) ^ (N + 1) * Real.exp (Real.pi * |t| / 2) *
        ‖spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I)‖) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hκ hH

end
end ArtinMatthews
