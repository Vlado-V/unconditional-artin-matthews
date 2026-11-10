module

public import ArtinMatthews.GiantTwoSidedResidueLoss
public import ArtinMatthews.GiantTwoSidedLabelOffsets
public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
public import ArtinMatthews.ScalarWeightedResidueCRT
public import ArtinMatthews.MarkedBonferroniTail
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

/-! The actual source visit schedule and grouped repeated-offset loss satisfy
the scalar sieve hypotheses at the source moment length. -/

namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

def giantSourceResidueLoss (x q : ℝ)
    (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ) (p a : ℕ) : ℝ :=
  giantTwoSidedResidueLossNat univ
    (markedMemoryVisitQ q (giantTwoSidedSourceMomentLength x)) offset p a

def giantSourceInactivePrimes (x : ℝ) (S : Finset (GiantCandidateGroupIndex x)) {M : ℕ}
    (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
      MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M) : Finset ℕ :=
  markedPhysicalBandPrimes (fun i : S => giantCandidateGroup x i.val) \
    markedPhysicalPathUsedPrimes univ labels

def giantSourceResidueMeanBudget (x : ℝ) : ℝ :=
  ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) *
    giantCandidateGroupLogRate * Real.log (Real.log x)

theorem giantSourceVisitQ_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) (v : Fin (n + 1)) :
    0 ≤ markedMemoryVisitQ q n v ∧ markedMemoryVisitQ q n v ≤ 1 := by
  have h := markedMemoryEta_mem_unitInterval hq0 hq1 n v
  unfold markedMemoryEta at h
  constructor <;> linarith

theorem giantSourceResidueLoss_bounds {x q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ) (p a : ℕ) :
    0 ≤ giantSourceResidueLoss x q offset p a ∧ giantSourceResidueLoss x q offset p a ≤ 1 :=
  giantTwoSidedResidueLoss_bounds univ _ (fun v _ => giantSourceVisitQ_bounds hq0 hq1 _ v)
    offset p (a : ZMod p)

theorem giantSourceResidueMass_le {x q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ) {p : ℕ} (hp : 0 < p) :
    scalarWeightedResidueMass (giantSourceResidueLoss x q offset) p ≤
      ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) := by
  let : NeZero p := ⟨hp.ne'⟩
  simpa only [scalarWeightedResidueMass, giantSourceResidueLoss, card_univ, Fintype.card_fin]
    using giantTwoSidedResidueLoss_mass_le_visits univ _
      (fun v _ => giantSourceVisitQ_bounds hq0 hq1 _ v) offset p

theorem giantSourceResidueMean_le {x q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ) {p : ℕ} (hp : 0 < p) :
    scalarWeightedResidueMean (giantSourceResidueLoss x q offset) p ≤
      ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) / p :=
  div_le_div_of_nonneg_right (giantSourceResidueMass_le hq0 hq1 offset hp) (Nat.cast_nonneg _)

theorem giantSourceInactivePrimes_subset (x : ℝ) (S : Finset (GiantCandidateGroupIndex x))
    {M : ℕ} (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
      MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M) :
    giantSourceInactivePrimes x S labels ⊆ giantCandidateFullPrimes x := by
  intro p hp
  exact giantCandidateSelectedGroups_union_subset S (mem_sdiff.mp hp).1

theorem giantSourceVisits_le {x : ℝ} (hL : 1 ≤ Real.log x) :
    ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) ≤
      5 * (Real.log x) ^ (13 / 25 : ℝ) := by
  have hn := giantTwoSidedSourceMomentLength_le hL
  have hp := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 13 / 25)
  push_cast
  linarith

theorem giantSourceResidueMean_cap :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ)
        (p : ℕ), p ∈ giantCandidateFullPrimes x →
        scalarWeightedResidueMean (giantSourceResidueLoss x q offset) p ≤ 2 / 3 := by
  have hlim : Tendsto (fun L : ℝ => 5 * L ^ (13 / 25 : ℝ) /
      Real.exp (L ^ (28 / 100 : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul, neg_mul, Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_zero] using
      (rpow_mul_exp_neg_rpow_tendsto (13 / 25) (δ := 28 / 100) (b := 1)
        (by norm_num) (by norm_num)).const_mul 5
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (hlim.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2 / 3))]
    with x hx hL hsmall
  intro q hq0 hq1 offset p hp
  obtain ⟨hprime, hlo, _⟩ := giantCandidateFullPrimes_range hx hL hp
  calc
    _ ≤ ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) / p :=
      giantSourceResidueMean_le hq0 hq1 offset hprime.pos
    _ ≤ 5 * (Real.log x) ^ (13 / 25 : ℝ) /
        Real.exp ((Real.log x) ^ (28 / 100 : ℝ)) :=
      div_le_div₀ (by positivity) (giantSourceVisits_le hL) (Real.exp_pos _) hlo
    _ ≤ 2 / 3 := hsmall.le

theorem giantSourceResidueMean_sum :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x))
      (M : ℕ) (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
        MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M)
      (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ,
        (∑ p ∈ giantSourceInactivePrimes x S labels,
          scalarWeightedResidueMean (giantSourceResidueLoss x q offset) p) ≤
            giantSourceResidueMeanBudget x := by
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateGroup_total_count_eventually, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hgeo hcount hx hL
  intro S M labels q hq0 hq1 offset
  let B := markedPhysicalBandPrimes (fun i : S => giantCandidateGroup x i.val)
  let R := giantSourceInactivePrimes x S labels
  let V : ℝ := ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ)
  have hmass : (∑ p ∈ B, 1 / (p : ℝ)) ≤ (S.card : ℝ) := by
    dsimp only [B, markedPhysicalBandPrimes]
    rw [sum_biUnion (fun i _ j _ hij => (hgeo S).1 hij)]
    calc
      _ ≤ ∑ _i : S, (1 : ℝ) := sum_le_sum (fun i _ => (hgeo S).2.1 i |>.2.le)
      _ = _ := by simp
  have hR : (∑ p ∈ R, 1 / (p : ℝ)) ≤ (S.card : ℝ) :=
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)).trans hmass
  have hcard : (S.card : ℝ) ≤ giantCandidateGroupLogRate * Real.log (Real.log x) :=
    (Nat.cast_le.mpr (card_le_univ S)).trans hcount
  calc
    _ ≤ ∑ p ∈ R, V / p := by
      apply sum_le_sum
      intro p hp
      exact giantSourceResidueMean_le hq0 hq1 offset
        (giantCandidateFullPrimes_range hx hL (giantSourceInactivePrimes_subset x S labels hp)).1.pos
    _ = V * ∑ p ∈ R, 1 / (p : ℝ) := by rw [mul_sum]; apply sum_congr rfl; intro p _; ring
    _ ≤ V * (S.card : ℝ) := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
    _ ≤ V * (giantCandidateGroupLogRate * Real.log (Real.log x)) :=
      mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    _ = giantSourceResidueMeanBudget x := by
      dsimp [V, giantSourceResidueMeanBudget]
      ring

end
end ArtinMatthews
