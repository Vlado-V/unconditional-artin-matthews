module

public import ArtinMatthews.ShiftedABLCorrelationTarget
public import ArtinMatthews.ShiftedABLLevelRemoval
public import ArtinMatthews.CubicThetaActualReal
public import ArtinMatthews.ShiftedBilinearGlobal
public import ArtinMatthews.ShiftedRawDyadicEstimate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews
open Set OAI.SevenEighths
open scoped ContDiff
noncomputable section

theorem giantSamplingCoprimeShiftedBilinearBound_of_correlation
    (N : ℕ) (η : HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff η n) = idealThetaCoeff η n)
    (hsource : ShiftedABLCorrelationSource N η)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingCoprimeShiftedBilinearBound N η Φ x ν Cν :=
  giantSamplingCoprimeShiftedBilinearBound_of_dyadic N η Φ hΦ hsupp
    (shiftedRawDyadicBound_of_correlation N η hreal hsource)

theorem giantSamplingShiftedBilinearBound_of_correlation
    (N : ℕ) (hN : N ≠ 0) (η : HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff η n) = idealThetaCoeff η n)
    (hsource : ShiftedABLCorrelationSource N η)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingShiftedBilinearBound η Φ x ν Cν := by
  intro ν hν
  obtain ⟨C, hC, hbound⟩ := giantSamplingCoprimeShiftedBilinearBound_of_correlation
    N η hreal hsource Φ hΦ hsupp ν hν
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨(N : ℝ) ^ 2 * C, mul_pos (sq_pos_of_pos hN0) hC, ?_⟩
  intro x hx
  exact giantSamplingShiftedBilinearBound_of_coprime N hN η Φ
    (zero_le_one.trans hx) hC.le (hbound x hx)

theorem cubicNumerator_shiftedBilinearBound_of_correlation
    (a : ℤ) (ha : a ≠ 0)
    (hsource : ShiftedABLCorrelationSource (cubicNumeratorThetaLevel a)
      (cubicNumeratorHeckeCharacter a ha))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter a ha) Φ x ν Cν :=
  giantSamplingShiftedBilinearBound_of_correlation (cubicNumeratorThetaLevel a)
    (cubicNumeratorThetaLevel_ne_zero ha) (cubicNumeratorHeckeCharacter a ha)
    (cubicNumeratorThetaCoeff_conjugate a ha) hsource Φ hΦ hsupp

end
end ArtinMatthews
