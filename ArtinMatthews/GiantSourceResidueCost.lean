module

public import ArtinMatthews.GiantSourceResidueMass
public import ArtinMatthews.ScalarWeightedBonferroni
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedProgressionGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ENatToNat
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

/-! The explicit source sieve depth and its actual coefficient cost. -/

namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

def giantSourceResidueRate (A : ℝ) : ℝ :=
  (10 * giantCandidateGroupLogRate + 2 * A + 1) / Real.log 2

def giantSourceResidueDepth (A x : ℝ) : ℕ :=
  ⌈giantSourceResidueRate A * ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) *
    Real.log (Real.log x)⌉₊

def giantSourceResidueOrder (A x : ℝ) : ℕ := giantSourceResidueDepth A x - 1

def giantSourceResidueCostRate (A : ℝ) : ℝ := 3 * (5 * giantSourceResidueRate A + 1)

theorem giantSourceResidueRate_pos {A : ℝ} (hA : 0 ≤ A) : 0 < giantSourceResidueRate A := by
  unfold giantSourceResidueRate giantCandidateGroupLogRate
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem giantSourceResidueOrder_succ {A x : ℝ} (hA : 0 ≤ A) (hL : 1 < Real.log x) :
    giantSourceResidueOrder A x + 1 = giantSourceResidueDepth A x := by
  unfold giantSourceResidueOrder
  apply Nat.sub_add_cancel
  apply Nat.ceil_pos.mpr
  exact mul_pos (mul_pos (giantSourceResidueRate_pos hA) (by positivity)) (Real.log_pos hL)

theorem giantSourceResidueDepth_lower {A x : ℝ} (hA : 0 ≤ A) (hL : 1 < Real.log x) :
    5 * giantSourceResidueMeanBudget x ≤
        (giantSourceResidueDepth A x : ℝ) * Real.log 2 / 2 ∧
      2 * A * (giantTwoSidedSourceMomentLength x : ℝ) * Real.log (Real.log x) ≤
        (giantSourceResidueDepth A x : ℝ) * Real.log 2 := by
  let V : ℝ := ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ)
  let R := giantCandidateGroupLogRate
  have hR : 0 < R := by dsimp [R, giantCandidateGroupLogRate]; positivity
  have hV : 0 ≤ V := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (Real.log x) := (Real.log_pos hL).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoeff : 0 ≤ 10 * R + 2 * A + 1 := by positivity
  have hlow : (10 * R + 2 * A + 1) * V * Real.log (Real.log x) ≤
      (giantSourceResidueDepth A x : ℝ) * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right
      (Nat.le_ceil (giantSourceResidueRate A * V * Real.log (Real.log x))) hlog2.le
    convert hh using 1
    · dsimp [giantSourceResidueRate, R]
      field_simp [hlog2.ne']
    · rfl
  constructor
  · have hh : 10 * giantSourceResidueMeanBudget x ≤
        (10 * R + 2 * A + 1) * V * Real.log (Real.log x) := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show 10 * R ≤ 10 * R + 2 * A + 1 by linarith) hV) hlog
      simpa only [giantSourceResidueMeanBudget, V, R, mul_assoc, mul_left_comm, mul_comm] using h
    linarith [hh.trans hlow]
  · have hNV : (giantTwoSidedSourceMomentLength x : ℝ) ≤ V := by dsimp [V]; push_cast; linarith
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul (show 2 * A ≤ 10 * R + 2 * A + 1 by linarith)
        hNV (Nat.cast_nonneg _) hcoeff) hlog
    exact hh.trans hlow

theorem giantSourceResidueParameter_upper (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      (giantSourceResidueDepth A x : ℝ) ≤
          (5 * giantSourceResidueRate A + 1) * (Real.log x) ^ (53 / 100 : ℝ) ∧
        giantSourceResidueMeanBudget x ≤
          5 * giantCandidateGroupLogRate * (Real.log x) ^ (53 / 100 : ℝ) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).bound
    (zero_lt_one : (0 : ℝ) < 1)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually hlog] with x hL hlog
  have hL0 : 0 < Real.log x := zero_lt_one.trans_le hL
  have hlog0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hl : Real.log (Real.log x) ≤ (Real.log x) ^ (1 / 100 : ℝ) := by
    change ‖Real.log (Real.log x)‖ ≤ 1 * ‖(Real.log x) ^ (1 / 100 : ℝ)‖ at hlog
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _)] using hlog
  have hpow : (Real.log x) ^ (13 / 25 : ℝ) * (Real.log x) ^ (1 / 100 : ℝ) =
      (Real.log x) ^ (53 / 100 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hV := giantSourceVisits_le hL
  have hD : 0 ≤ giantSourceResidueRate A := (giantSourceResidueRate_pos hA).le
  have hR : 0 ≤ giantCandidateGroupLogRate := by unfold giantCandidateGroupLogRate; positivity
  have hprod : ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) * Real.log (Real.log x) ≤
      5 * (Real.log x) ^ (53 / 100 : ℝ) := by
    calc
      _ ≤ (5 * (Real.log x) ^ (13 / 25 : ℝ)) * (Real.log x) ^ (1 / 100 : ℝ) :=
        mul_le_mul hV hl hlog0 (by positivity)
      _ = _ := by rw [mul_assoc, hpow]
  constructor
  · have hc := (Nat.ceil_lt_add_one
      (mul_nonneg (mul_nonneg hD
        (Nat.cast_nonneg (giantTwoSidedSourceMomentLength x + 1))) hlog0)).le
    change (giantSourceResidueDepth A x : ℝ) ≤
      giantSourceResidueRate A * ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) *
        Real.log (Real.log x) + 1 at hc
    have hp1 := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 53 / 100)
    have hh := mul_le_mul_of_nonneg_left hprod hD
    nlinarith only [hc, hp1, hh]
  · have hh := mul_le_mul_of_nonneg_left hprod hR
    dsimp [giantSourceResidueMeanBudget]
    nlinarith only [hh]

theorem giantSourceVisits_le_exp :
    ∀ᶠ x : ℝ in atTop,
      ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ) ≤
        Real.exp ((Real.log x) ^ (45 / 100 : ℝ)) := by
  have hlim : Tendsto (fun L : ℝ => 5 * L ^ (13 / 25 : ℝ) /
      Real.exp (L ^ (45 / 100 : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul, neg_mul, Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_zero] using
      (rpow_mul_exp_neg_rpow_tendsto (13 / 25) (δ := 45 / 100) (b := 1)
        (by norm_num) (by norm_num)).const_mul 5
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (hlim.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with x hL hsmall
  exact (giantSourceVisits_le hL).trans
    ((div_le_one (Real.exp_pos _)).mp hsmall.le)

theorem giantSourceInactivePrimes_card {x : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x)
    (S : Finset (GiantCandidateGroupIndex x)) {M : ℕ}
    (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
      MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M) :
    ((giantSourceInactivePrimes x S labels).card : ℝ) ≤
      Real.exp ((Real.log x) ^ (45 / 100 : ℝ)) := by
  let Z := Real.exp ((Real.log x) ^ (45 / 100 : ℝ))
  have hcard : (giantSourceInactivePrimes x S labels).card ≤ ⌊Z⌋₊ := by
    calc
      _ ≤ (Icc 1 ⌊Z⌋₊).card := card_le_card (by
        intro p hp
        have hh := giantCandidateFullPrimes_range hx hL (giantSourceInactivePrimes_subset x S labels hp)
        exact mem_Icc.mpr ⟨hh.1.pos, (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hh.2.2.le⟩)
      _ = _ := by simp
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (Real.exp_nonneg _))

theorem giantSourceResidueEndpoint_cost (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x))
      (M : ℕ) (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
        MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M)
      (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ,
        scalarWeightedResidueEndpointMass (giantSourceInactivePrimes x S labels)
          (giantSourceResidueLoss x q offset) (giantSourceResidueDepth A x) ≤
            Real.exp (giantSourceResidueCostRate A * (Real.log x) ^ (49 / 50 : ℝ)) := by
  filter_upwards [giantSourceResidueParameter_upper A hA, giantSourceVisits_le_exp,
    eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hparam hvisit hx hL
  intro S M labels q hq0 hq1 offset
  let P := giantSourceInactivePrimes x S labels
  let f := giantSourceResidueLoss x q offset
  let h := giantSourceResidueDepth A x
  let V : ℝ := ((giantTwoSidedSourceMomentLength x + 1 : ℕ) : ℝ)
  let t := (Real.log x) ^ (45 / 100 : ℝ)
  have hL0 : 0 < Real.log x := zero_lt_one.trans_le hL
  have ht : 1 ≤ t := Real.one_le_rpow hL (by norm_num)
  have hbase : max 1 ((P.card : ℝ) * V) ≤ Real.exp (2 * t) := by
    apply max_le
    · exact Real.one_le_exp_iff.mpr (by positivity)
    · calc
        _ ≤ Real.exp t * Real.exp t :=
          mul_le_mul (giantSourceInactivePrimes_card hx hL S labels) hvisit
            (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmass : scalarWeightedResidueEndpointMass P f h ≤
      (h + 1 : ℝ) * (max 1 ((P.card : ℝ) * V)) ^ h :=
    scalarWeightedResidueEndpointMass_le P f
      (fun p _ r _ => (giantSourceResidueLoss_bounds hq0 hq1 offset p r).1) h V
      (Nat.cast_nonneg _) (fun p hp => giantSourceResidueMass_le hq0 hq1 offset
        (giantCandidateFullPrimes_range hx hL (giantSourceInactivePrimes_subset x S labels hp)).1.pos)
  calc
    _ ≤ (h + 1 : ℝ) * (max 1 ((P.card : ℝ) * V)) ^ h := hmass
    _ ≤ Real.exp (h : ℝ) * (Real.exp (2 * t)) ^ h :=
      mul_le_mul (Real.add_one_le_exp (h : ℝ))
        (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hbase h)
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((h : ℝ) + (h : ℝ) * (2 * t)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (3 * (h : ℝ) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ (h : ℝ))]
    _ ≤ Real.exp (3 * ((5 * giantSourceResidueRate A + 1) *
        (Real.log x) ^ (53 / 100 : ℝ)) * t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hparam.1 (by norm_num)) (by positivity)
    _ = _ := by
      congr 1
      unfold giantSourceResidueCostRate
      dsimp [t]
      rw [show (49 / 50 : ℝ) = 53 / 100 + 45 / 100 by norm_num, Real.rpow_add hL0]
      ring

def giantSourceResidueTotalCostRate (A : ℝ) (M : ℕ) : ℝ :=
  giantSourceResidueCostRate A + 5 * M * giantCandidateGroupLogRate +
    15 * giantCandidateGroupLogRate

theorem giantSourceResidueCost_budget (A : ℝ) (hA : 0 ≤ A) (M : ℕ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,
      giantSourceResidueCostRate A * (Real.log x) ^ (49 / 50 : ℝ) +
        (5 * M * giantCandidateGroupLogRate) * (Real.log x) ^ (49 / 50 : ℝ) +
        3 * giantSourceResidueMeanBudget x ≤ (γ / 2) * Real.log x / 2 := by
  filter_upwards [giantSourceResidueParameter_upper A hA,
    marked_sublinear_log_exp_le_rpow_eventually (49 / 50)
      (giantSourceResidueTotalCostRate A M) (γ / 4) (by norm_num) (by positivity),
    eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hparam hsmall hx hL
  have hR : 0 ≤ giantCandidateGroupLogRate := by unfold giantCandidateGroupLogRate; positivity
  have hmean : giantSourceResidueMeanBudget x ≤
      5 * giantCandidateGroupLogRate * (Real.log x) ^ (49 / 50 : ℝ) :=
    hparam.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (53 / 100 : ℝ) ≤ 49 / 50))
      (by positivity))
  have hexponent : giantSourceResidueTotalCostRate A M * (Real.log x) ^ (49 / 50 : ℝ) ≤
      Real.log x * (γ / 4) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)] at hsmall
    exact Real.exp_le_exp.mp hsmall
  calc
    _ ≤ giantSourceResidueTotalCostRate A M * (Real.log x) ^ (49 / 50 : ℝ) := by
      dsimp [giantSourceResidueTotalCostRate]
      nlinarith only [hmean]
    _ ≤ Real.log x * (γ / 4) := hexponent
    _ = _ := by ring

end
end ArtinMatthews
