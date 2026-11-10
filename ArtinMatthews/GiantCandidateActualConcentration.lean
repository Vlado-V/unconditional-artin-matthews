module

public import ArtinMatthews.GiantCandidateFailedDyadLimit
public import ArtinMatthews.GiantCandidateBoxSuccessMoments
public import ArtinMatthews.GiantCandidateFailedBoxConcentration
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

/-! The actual rough-box concentration discards a negligible mass from
the original weighted tuples before their signed expansion. -/

namespace ArtinMatthews
noncomputable section
open Filter
open scoped Asymptotics

theorem giant_candidate_uniformFailedBoxDecay_actual {γ q : ℝ}
    (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) :
    ∃ threshold : ℝ, 0 < threshold ∧ GiantCandidateUniformFailedBoxDecay γ q threshold j := by
  obtain ⟨β, hβ, hmoments⟩ :=
    giant_candidate_box_success_moments_eventually (γ/2) (half_pos hγ) hq0 hq1 hj
  exact giant_candidate_uniformFailedBoxDecay_of_success_moments hγ hq0 hq1 j hj hβ hmoments

theorem giant_candidate_failedProxyMass_isLittleO_actual {γ q : ℝ}
    (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∀ T : ℝ, 0 < T →
      (fun x : ℝ =>
        giantCandidateFailedProxyMass x threshold (giantCandidateCoinScale q j) q T γ j)
        =o[atTop] (fun x : ℝ => x / Real.log x) := by
  obtain ⟨threshold, ht, hmean⟩ := giant_candidate_uniformFailedBoxDecay_actual hγ hq0 hq1 j hj
  exact ⟨threshold, ht, fun _ hT =>
    giant_candidate_failedProxyMass_isLittleO_of_dyad_mean hT hγ hq0 hq1 j hj hmean⟩

end
end ArtinMatthews
