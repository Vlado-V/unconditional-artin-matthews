module

public import ArtinMatthews.GiantCandidateCoinExpansion
public import ArtinMatthews.GiantCandidateDyadBudget
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

/-! The performed signed expansion has a fixed logarithmic cost. Both
family lower bounds pass from each retained success set to its active
union. The original signs, coin scale, and allocation factors stay in
the sum. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Asymptotics

variable {J : Type*} [Fintype J] (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (threshold : ℝ)
variable (hq0 : 0 ≤ q) (hq1 : q < 1) (hj : 0 < j)
variable (hactive : ∀ A : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ S ∈ giantCandidateRetainedOutcomes x threshold,
      ‖giantCandidateActualUnguardedShiftedCorrelation (giantCandidateFullPrimes x)
        (fun i : S => giantCandidateGroup x i.val) e χ ε Φ T γ q j x‖ ≤ (Real.log x)^(-A))

include hq0 hq1 hj hactive in
theorem giantCandidateSignedCorrelationSum_log_saving_of_active (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ‖giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold
        (giantCandidateCoinScale q j) q‖ ≤ x * (Real.log x)^(-A) := by
  let c := giantCandidateCoinScale q j
  obtain ⟨hc0, hc1, _⟩ := giantCandidateCoinScale_bounds hq0 hq1 j hj
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc0.le, hc1⟩
  let b := giantCandidateGroupLogRate * Real.log 3
  let r := giantCandidateGroupLogRate * Real.log (j : ℝ)
  let D := A + (b + r)
  filter_upwards [hactive D, giantCandidateCoinTerms_card_log_eventually,
    giantCandidateSelectedGroups_exponential_cost_eventually (j : ℝ) (Nat.one_le_cast.mpr hj),
    eventually_gt_atTop (1 : ℝ)] with x hcorr hcard hjcost hx
  let L := Real.log x
  let E := giantCandidateCoinTerms x threshold
  let S (p : GiantCandidateCoinTerm x) := p.1 ∪ p.2
  let C (p : GiantCandidateCoinTerm x) :=
    giantCandidateActualUnguardedShiftedCorrelation (giantCandidateFullPrimes x)
      (fun i : S p => giantCandidateGroup x i.val) e χ ε Φ T γ q j x
  let alloc (p : GiantCandidateCoinTerm x) := (j : ℂ)^(S p).card / j.factorial
  let f (p : GiantCandidateCoinTerm x) :=
    giantCandidateCoinTermCoefficient x c p * (alloc p * ((x : ℂ) * C p))
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  have hL : 0 < L := Real.log_pos hx
  have hxnorm : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have halloc (p : GiantCandidateCoinTerm x) : ‖alloc p‖ ≤ L^r := by
    calc
      _ = (j : ℝ)^(S p).card / (j.factorial : ℝ) := by
        dsimp only [alloc]
        rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
      _ ≤ (j : ℝ)^(S p).card :=
        div_le_self (by positivity) (Nat.one_le_cast.mpr (Nat.factorial_pos j))
      _ ≤ _ := hjcost (S p)
  have hterm (p : GiantCandidateCoinTerm x) (hp : p ∈ E) :
      ‖f p‖ ≤ L^r * (x * L^(-D)) := by
    have hCp : ‖C p‖ ≤ L^(-D) := hcorr (S p) (giantCandidateCoinTerms_active_retained hp)
    calc
      _ = ‖giantCandidateCoinTermCoefficient x c p‖ * (‖alloc p‖ * (x * ‖C p‖)) := by
        simp only [f, norm_mul, hxnorm]
      _ ≤ ‖alloc p‖ * (x * ‖C p‖) :=
        mul_le_of_le_one_left (by positivity) (giantCandidateCoinTermCoefficient_norm_le_one x hc p)
      _ ≤ _ := mul_le_mul (halloc p) (mul_le_mul_of_nonneg_left hCp hx0)
        (mul_nonneg hx0 (norm_nonneg _)) (Real.rpow_nonneg hL.le _)
  change ‖∑ p ∈ E, f p‖ ≤ x * L^(-A)
  calc
    _ ≤ ∑ p ∈ E, ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ E, L^r * (x * L^(-D)) := sum_le_sum hterm
    _ = (E.card : ℝ) * (L^r * (x * L^(-D))) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ L^b * (L^r * (x * L^(-D))) := mul_le_mul_of_nonneg_right (hcard threshold) (by positivity)
    _ = x * ((L^b * L^r) * L^(-D)) := by ring
    _ = _ := by rw [← Real.rpow_add hL, ← Real.rpow_add hL]; congr 2; dsimp only [D]; ring

include hq0 hq1 hj hactive in
theorem giant_candidate_signedCorrelationSum_isLittleO_of_active :
    (fun x : ℝ => giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold
      (giantCandidateCoinScale q j) q) =o[atTop] (fun x : ℝ => x / Real.log x) := by
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO giantCandidateLogTenth_isLittleO
  filter_upwards [giantCandidateSignedCorrelationSum_log_saving_of_active e χ ε Φ T γ q j
      threshold hq0 hq1 hj hactive (11/10),
    eventually_gt_atTop (1 : ℝ)] with x h hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  have hL := Real.log_pos hx
  have hpow : (Real.log x)^(-(11/10 : ℝ)) =
      (Real.log x)^(-(1/10 : ℝ)) / Real.log x := by
    rw [show -(11/10 : ℝ) = -(1/10 : ℝ) - 1 by norm_num, Real.rpow_sub hL, Real.rpow_one]
  simp only [one_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ x * (Real.log x)^(-(1/10 : ℝ)) / Real.log x)]
  rw [hpow, ← mul_div_assoc] at h
  exact h

end
end ArtinMatthews
