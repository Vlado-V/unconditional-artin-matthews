module

public import ArtinMatthews.GiantCandidateCoinPartition
public import ArtinMatthews.GiantCandidateCoinSuccess
public import ArtinMatthews.GiantCandidateCoinSets
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

/-! The literal retained and failed masses split the original nonnegative
coin partition before any signed expansion. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateRetainedCoinMass (x threshold c q : ℝ) (j v : ℕ) : ℝ :=
  ∑ S ∈ giantCandidateRetainedOutcomes x threshold,
    giantCoinOutcomeWeight univ (giantCandidateCoinSuccess x c q j v) S

def giantCandidateFailedCoinMass (x threshold c q : ℝ) (j v : ℕ) : ℝ :=
  ∑ S ∈ (univ : Finset (GiantCandidateGroupIndex x)).powerset \
      giantCandidateRetainedOutcomes x threshold,
    giantCoinOutcomeWeight univ (giantCandidateCoinSuccess x c q j v) S

theorem giantCandidateCoinMass_partition (x threshold c q : ℝ) (j v : ℕ) :
    giantCandidateRetainedCoinMass x threshold c q j v +
      giantCandidateFailedCoinMass x threshold c q j v = 1 := by
  apply giantCoinOutcomeWeight_retained_failed
  exact filter_subset _ _

theorem giantCandidateCoinMass_actual_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    ∀ᶠ x : ℝ in atTop,∀ (threshold : ℝ) (v : ℕ),
      let c := giantCandidateCoinScale q j
      giantCandidateRetainedCoinMass x threshold c q j v ∈ Set.Icc (0:ℝ) 1 ∧
      giantCandidateFailedCoinMass x threshold c q j v ∈ Set.Icc (0:ℝ) 1 := by
  filter_upwards [giantCandidateCoinSuccess_actual_unitInterval hq0 hq1 j hj] with x hx
  intro threshold v
  let c := giantCandidateCoinScale q j
  let U := (univ : Finset (GiantCandidateGroupIndex x))
  let s := giantCandidateCoinSuccess x c q j v
  let R := giantCandidateRetainedOutcomes x threshold
  have hnonneg (S : Finset (GiantCandidateGroupIndex x)) :
      0 ≤ giantCoinOutcomeWeight U s S :=
    giantCoinOutcomeWeight_nonneg U s S (subset_univ _) (fun i _ => hx i v)
  have hR : 0 ≤ giantCandidateRetainedCoinMass x threshold c q j v :=
    sum_nonneg (fun S _ => hnonneg S)
  have hF : 0 ≤ giantCandidateFailedCoinMass x threshold c q j v :=
    sum_nonneg (fun S _ => hnonneg S)
  have hs := giantCandidateCoinMass_partition x threshold c q j v
  exact ⟨⟨hR,by linarith only [hs,hF]⟩,⟨hF,by linarith only [hs,hR]⟩⟩

theorem giantCandidateRetainedCoinMass_eq_signed (x threshold c q : ℝ) (j v : ℕ) :
    (giantCandidateRetainedCoinMass x threshold c q j v:ℂ) =
      ∑ p ∈ giantCandidateCoinTerms x threshold,
        giantCandidateCoinTermCoefficient x c p *
          (giantCandidateActiveOneMark (fun i : ↥(p.1 ∪ p.2) => giantCandidateGroup x i.val) q (v-1):ℂ) *
          (giantCandidateActiveOneMark (fun i : ↥(p.1 ∪ p.2) => giantCandidateGroup x i.val) (q/(j:ℝ)) v:ℂ) := by
  rw [giantCandidateRetainedCoinMass,Complex.ofReal_sum,giantCandidateCoinTerms,Finset.sum_sigma]
  apply sum_congr rfl
  intro S _
  rw [giantCoinOutcomeWeight_expand,Complex.ofReal_sum]
  apply sum_congr rfl
  intro T _
  rw [giantCandidateCoinSuccess_prod]
  push_cast
  unfold giantCandidateCoinTermCoefficient
  ring

end
end ArtinMatthews
