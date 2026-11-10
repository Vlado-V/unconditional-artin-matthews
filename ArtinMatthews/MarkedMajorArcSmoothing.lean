module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete piecewise-linear smoothing for the long coefficient.
This cutoff is a finite difference of first-order Riesz weights, so its
Mellin transform can be handled with an absolutely convergent contour. -/
namespace ArtinMatthews

open Finset

noncomputable def markedRieszCutoff (x t : ℝ) : ℝ := max (x-t) 0 / x

noncomputable def markedSmoothedStep (ε x t : ℝ) : ℝ :=
  (max ((1+ε)*x-t) 0 - max (x-t) 0) / (ε*x)

lemma marked_smoothed_step_riesz {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) (t : ℝ) :
    markedSmoothedStep ε x t =
      ((1+ε)*markedRieszCutoff ((1+ε)*x) t-markedRieszCutoff x t)/ε := by
  unfold markedSmoothedStep markedRieszCutoff
  have hε1 : (1+ε) ≠ 0 := by positivity
  field_simp

lemma marked_smoothed_step_one {ε x t : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (ht : t ≤ x) :
    markedSmoothedStep ε x t = 1 := by
  have hx' : x ≤ (1+ε)*x := by nlinarith
  unfold markedSmoothedStep
  rw [max_eq_left (by linarith : 0 ≤ (1+ε)*x-t),
    max_eq_left (by linarith : 0 ≤ x-t)]
  field_simp
  ring

lemma marked_smoothed_step_zero {ε x t : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (ht : (1+ε)*x ≤ t) :
    markedSmoothedStep ε x t = 0 := by
  have hx' : x ≤ (1+ε)*x := by nlinarith
  simp only [markedSmoothedStep, max_eq_right (by linarith : (1+ε)*x-t ≤ 0),
    max_eq_right (by linarith : x-t ≤ 0), sub_self, zero_div]

lemma marked_smoothed_step_bounds {ε x : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (t : ℝ) :
    0 ≤ markedSmoothedStep ε x t ∧ markedSmoothedStep ε x t ≤ 1 := by
  by_cases ht : t ≤ x
  · rw [marked_smoothed_step_one hε hx ht]; norm_num
  by_cases ht' : (1+ε)*x ≤ t
  · rw [marked_smoothed_step_zero hε hx ht']; norm_num
  have htlo : x < t := lt_of_not_ge ht
  have hthi : t < (1+ε)*x := lt_of_not_ge ht'
  unfold markedSmoothedStep
  rw [max_eq_left (by linarith : 0 ≤ (1+ε)*x-t),
    max_eq_right (by linarith : x-t ≤ 0), sub_zero]
  constructor
  · positivity
  · apply (div_le_one (mul_pos hε hx)).mpr
    nlinarith

/-- The error occurs only in the explicit interval immediately to the right
of the sharp endpoint, and has size at most one. -/
lemma marked_smoothed_step_error {ε x : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (t : ℝ) :
    |markedSmoothedStep ε x t - (if t ≤ x then 1 else 0)| ≤
      if x < t ∧ t < (1+ε)*x then 1 else 0 := by
  by_cases ht : t ≤ x
  · rw [marked_smoothed_step_one hε hx ht]
    simp [ht, not_lt.mpr ht]
  have htlo : x < t := lt_of_not_ge ht
  by_cases hthi : t < (1+ε)*x
  · simp only [ht, ite_false, sub_zero, htlo, hthi, and_self, ite_true]
    rw [abs_of_nonneg (marked_smoothed_step_bounds hε hx t).1]
    exact (marked_smoothed_step_bounds hε hx t).2
  · rw [marked_smoothed_step_zero hε hx (le_of_not_gt hthi)]
    simp [ht, hthi]

/-- Actual finite complex sums inherit precisely the boundary error, without
any cancellation assumption on the coefficients. -/
theorem marked_smoothed_prefix_sum_error {ε x : ℝ}
    (hε : 0 < ε) (hx : 0 < x) (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖(∑ n ∈ S, a n * (markedSmoothedStep ε x n : ℂ)) -
      ∑ n ∈ S, a n * (if (n:ℝ) ≤ x then 1 else 0)‖ ≤
      ∑ n ∈ S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x), ‖a n‖ := by
  classical
  rw [← sum_sub_distrib]
  calc
    _ = ‖∑ n ∈ S, a n * ((markedSmoothedStep ε x n : ℂ) -
        (if (n:ℝ) ≤ x then 1 else 0))‖ := by congr 1; apply sum_congr rfl; intro n hn; ring
    _ ≤ ∑ n ∈ S, ‖a n * ((markedSmoothedStep ε x n : ℂ) -
        (if (n:ℝ) ≤ x then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, if x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x then ‖a n‖ else 0 := by
      apply sum_le_sum
      intro n hn
      have hh := mul_le_mul_of_nonneg_left (marked_smoothed_step_error hε hx (n:ℝ))
        (norm_nonneg (a n))
      have he : (markedSmoothedStep ε x n : ℂ) - (if (n:ℝ) ≤ x then 1 else 0) =
          ((markedSmoothedStep ε x n - (if (n:ℝ) ≤ x then 1 else 0) : ℝ) : ℂ) := by
        split_ifs <;> push_cast <;> rfl
      rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_ite, mul_one, mul_zero] using hh
    _ = _ := by rw [sum_filter]

/-- Smoothing any subinterval costs only its two explicit boundary strips. -/
theorem marked_smoothed_interval_sum_error {ε u v : ℝ}
    (hε : 0 < ε) (hu : 0 < u) (huv : u ≤ v) (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖(∑ n ∈ S, a n * ((markedSmoothedStep ε v n - markedSmoothedStep ε u n : ℝ) : ℂ)) -
      ∑ n ∈ S, a n * (if u < (n:ℝ) ∧ (n:ℝ) ≤ v then 1 else 0)‖ ≤
      (∑ n ∈ S.filter (fun n : ℕ => v < (n:ℝ) ∧ (n:ℝ) < (1+ε)*v), ‖a n‖) +
      ∑ n ∈ S.filter (fun n : ℕ => u < (n:ℝ) ∧ (n:ℝ) < (1+ε)*u), ‖a n‖ := by
  classical
  have hind (n : ℕ) : (if u < (n:ℝ) ∧ (n:ℝ) ≤ v then (1:ℂ) else 0) =
      (if (n:ℝ) ≤ v then 1 else 0) - (if (n:ℝ) ≤ u then 1 else 0) := by
    by_cases hnu : (n:ℝ) ≤ u
    · have hnv : (n:ℝ) ≤ v := hnu.trans huv
      simp [hnu, hnv, not_lt.mpr hnu]
    · have hun : u < (n:ℝ) := lt_of_not_ge hnu
      by_cases hnv : (n:ℝ) ≤ v <;> simp [hnu, hun, hnv]
  simp only [Complex.ofReal_sub, hind, mul_sub, sum_sub_distrib]
  have he := norm_sub_le
    ((∑ n ∈ S, a n * (markedSmoothedStep ε v n : ℂ)) -
      ∑ n ∈ S, a n * (if (n:ℝ) ≤ v then 1 else 0))
    ((∑ n ∈ S, a n * (markedSmoothedStep ε u n : ℂ)) -
      ∑ n ∈ S, a n * (if (n:ℝ) ≤ u then 1 else 0))
  convert he.trans (add_le_add
    (marked_smoothed_prefix_sum_error hε (hu.trans_le huv) S a)
    (marked_smoothed_prefix_sum_error hε hu S a)) using 1
  congr 1
  ring

/-- The boundary strip contains at most its length plus one integer. -/
lemma marked_smoothing_boundary_card {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (S : Finset ℕ) :
    ((S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < y)).card : ℝ) ≤ y-x+1 := by
  classical
  have hsub : S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < y) ⊆
      Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    intro n hn
    obtain ⟨_,hlo,hhi⟩ := mem_filter.mp hn
    exact mem_Ioc.mpr ⟨(Nat.floor_lt hx).mpr hlo,
      (Nat.le_floor_iff (hx.trans hxy)).mpr hhi.le⟩
  have hcard : ((S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < y)).card : ℝ) ≤
      ((Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
  rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hxy)] at hcard
  have hlo := Nat.lt_floor_add_one x
  have hhi := Nat.floor_le (hx.trans hxy)
  linarith

/-- A uniform coefficient bound gives the explicit smoothing error used in
the long-prime estimate. -/
theorem marked_smoothed_interval_sum_error_bound {ε u v M : ℝ}
    (hε : 0 < ε) (hu : 0 < u) (huv : u ≤ v) (hM : 0 ≤ M)
    (S : Finset ℕ) (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ M) :
    ‖(∑ n ∈ S, a n * ((markedSmoothedStep ε v n - markedSmoothedStep ε u n : ℝ) : ℂ)) -
      ∑ n ∈ S, a n * (if u < (n:ℝ) ∧ (n:ℝ) ≤ v then 1 else 0)‖ ≤
      (ε*(u+v)+2)*M := by
  classical
  have hboundary (x : ℝ) (hx : 0 < x) :
      (∑ n ∈ S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x), ‖a n‖) ≤
      (ε*x+1)*M := by
    have hh := marked_smoothing_boundary_card hx.le
      (by nlinarith : x ≤ (1+ε)*x) S
    calc
      _ ≤ ∑ _n ∈ S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x), M :=
        sum_le_sum (fun n hn => ha n (mem_filter.mp hn).1)
      _ = ((S.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) < (1+ε)*x)).card : ℝ)*M := by
        simp
      _ ≤ ((1+ε)*x-x+1)*M := mul_le_mul_of_nonneg_right hh hM
      _ = _ := by ring
  have he := (marked_smoothed_interval_sum_error hε hu huv S a).trans
    (add_le_add (hboundary v (hu.trans_le huv)) (hboundary u hu))
  exact he.trans_eq (by ring)

end ArtinMatthews
