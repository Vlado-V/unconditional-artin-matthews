module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.MarkedProgressionGrowth
public import ArtinMatthews.PrimeExtractionWeightBounds
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

/-! The literal first endpoint of the two-sided correlation. Its norm is
bounded at fixed inert depth, and actual candidate primes preserve it. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateFirstEndpoint {J : Type*} [Fintype J] (e : J → ℝ)
    (ε x : ℝ) (n : ℕ) : ℂ :=
  (literalMarkedArrayWeight e x n : ℂ) * giantMarkedCenteredCore ε x n

theorem literalMarkedArrayWeight_mul_prime_of_outside {J : Type*} [Fintype J]
    (e : J → ℝ) (x : ℝ) {p : ℕ} (hp : p.Prime)
    (hout : ∀ i, p ∉ markedLogPowerBand (e i) x) (n : ℕ) :
    literalMarkedArrayWeight e x (p*n) = literalMarkedArrayWeight e x n := by
  unfold literalMarkedArrayWeight divisorWeight
  apply prod_congr rfl
  intro i _
  have h : activeDivisors (markedLogPowerBand (e i) x) (p*n) =
      activeDivisors (markedLogPowerBand (e i) x) n := by
    ext q
    simp only [activeDivisors, mem_filter]
    constructor
    · rintro ⟨hq, hd⟩
      have hqp := (mem_markedLogPowerBand.mp hq).1
      refine ⟨hq, ?_⟩
      rcases hqp.dvd_mul.mp hd with h | h
      · have he := (Nat.prime_dvd_prime_iff_eq hqp hp).mp h
        exact (hout i (he ▸ hq)).elim
      · exact h
    · rintro ⟨hq, hd⟩
      exact ⟨hq, dvd_mul_of_dvd_right hd p⟩
  unfold bandWeight bandCount
  rw [h]

theorem giantCandidateFirstEndpoint_mul_prime {J : Type*} [Fintype J]
    (e : J → ℝ) (ε x : ℝ) {p : ℕ} (hp : p.Prime)
    (hout : ∀ i, p ∉ markedLogPowerBand (e i) x)
    (hsmall : (p:ℝ) ≤ x^(1-ε)) (n : ℕ) :
    giantCandidateFirstEndpoint e ε x (p*n) = giantCandidateFirstEndpoint e ε x n := by
  by_cases hn : n = 0
  · simp only [hn, mul_zero]
  unfold giantCandidateFirstEndpoint giantMarkedCenteredCore
  rw [literalMarkedArrayWeight_mul_prime_of_outside e x hp hout,
    boundedGiantIndicator_mul_small hp.pos (Nat.pos_of_ne_zero hn) hsmall]

theorem giantCandidateFirstEndpoint_norm_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ x : ℝ in atTop,∀ n : ℕ,
      ‖giantCandidateFirstEndpoint e ε x n‖ ≤ (2 / Real.log 2) ^ Fintype.card J := by
  filter_upwards [literalMarkedArrayWeight_bound_eventually e (fun i => (he i).1),
    giantMarkedCenteredCore_interface e (fun i => (he i).2) hε hεq] with x hx hg
  intro n
  have hw := literalMarkedArrayWeight_nonneg e x n
  rw [giantCandidateFirstEndpoint,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
  exact (mul_le_of_le_one_right hw (hg.1 n)).trans (hx n)

theorem giantCandidateFirstEndpoint_active_invariant_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i, e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ p : ℕ, p.Prime →
      Real.exp ((Real.log x)^(27/100:ℝ)) ≤ (p:ℝ) →
      (p:ℝ) ≤ Real.exp ((Real.log x)^(46/100:ℝ)) →
      ∀ n, giantCandidateFirstEndpoint e ε x (p*n) = giantCandidateFirstEndpoint e ε x n := by
  have hpow := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/100)).comp
    Real.tendsto_log_atTop).eventually (eventually_gt_atTop (2:ℝ))
  filter_upwards [hpow, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    marked_sublinear_log_exp_le_rpow_eventually (46/100) 1 (1-ε) (by norm_num)
      (by linarith)] with x hpow hlog hsmall
  have hL : 0 < Real.log x := zero_lt_one.trans_le hlog
  change (2:ℝ) < (Real.log x)^(7/100:ℝ) at hpow
  have hsplit : (Real.log x)^(27/100:ℝ) =
      (Real.log x)^(1/5:ℝ) * (Real.log x)^(7/100:ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hlo : 2*(Real.log x)^(1/5:ℝ) < (Real.log x)^(27/100:ℝ) := by
    rw [hsplit,mul_comm (2:ℝ)]
    exact mul_lt_mul_of_pos_left hpow (Real.rpow_pos_of_pos hL _)
  intro p hp hpLo hpHi n
  apply giantCandidateFirstEndpoint_mul_prime e ε x hp _ _ n
  · intro i hi
    have hb := (mem_markedLogPowerBand.mp hi).2.2
    have hle : Real.exp (2*(Real.log x)^(e i)) ≤ Real.exp (2*(Real.log x)^(1/5:ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (he i))
        (by norm_num))
    exact (not_lt_of_ge (hpLo.trans (hb.trans hle))) (Real.exp_lt_exp.mpr hlo)
  · exact hpHi.trans (by simpa only [one_mul] using hsmall)

end
end ArtinMatthews
