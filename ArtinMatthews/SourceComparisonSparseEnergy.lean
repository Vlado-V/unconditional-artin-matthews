module

public import ArtinMatthews.MarkedSparsePhaseKernel
public import ArtinMatthews.MarkedSparseAbsorption
public import ArtinMatthews.MarkedSparseIntervalEnergy
public import ArtinMatthews.MarkedSparsePhaseContinuity
public import ArtinMatthews.MarkedSparsePhaseInterval
public import ArtinMatthews.MarkedSparsePhaseUniform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Sparse energy with the literal squared mass of the coefficient vector. -/

namespace ArtinMatthews

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Uniform separated sampling at exponential residual scale with a
subexponential number of times. -/
theorem sourceComparisonSparse_sample_energy (d b C Q : ℝ)
    (hd : 0 < d) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (U T : ℝ) (L R : ℕ) (S : Finset ℝ) (a : ℕ → ℂ),
        Real.exp (d*X) ≤ U → 0 ≤ T → T ≤ Real.exp (b*X) →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        (S.card:ℝ) ≤ Q*Real.exp (C*X^(91/(100:ℝ))) →
        (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t-u|) →
        (∀ t ∈ S, ∀ u ∈ S, |t-u| ≤ T) →
        (∑ t ∈ S, ‖markedDyadicPolynomial L R U a t‖^2) ≤ K*X*U*(∑ n ∈ Finset.Icc L R, ‖a n / U‖^2) := by
  let B : ℝ := 1+b/d
  have hB1 : 1 ≤ B := by
    have hh := div_nonneg hb hd.le
    dsimp [B]
    linarith
  have hBhalf : 1/2 ≤ B := by linarith
  obtain ⟨A,η,hA,hη,hηhalf,hrows⟩ := markedLogKernel_rows B hBhalf
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hrows
  have hscale : Tendsto (fun X : ℝ => Real.exp (d*X)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hd)
  let K : ℝ := A*(3+2*Real.log 2+2*b)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hscale.eventually (eventually_ge_atTop U₀),
    marked_sparse_power_error_absorption_mul Q C d η hd hη,
    eventually_ge_atTop (1:ℝ)] with X hXU₀ habsorb hX
  intro U T L R S a hU hT hTU hL hR hcard hsep hdiam
  have hX0 : 0 ≤ X := by linarith
  have hexp1 : 1 ≤ Real.exp (d*X) := Real.one_le_exp_iff.mpr (mul_nonneg hd.le hX0)
  have hU1 : 1 ≤ U := hexp1.trans hU
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hbX : 0 ≤ b*X := mul_nonneg hb hX0
  have hTpower : T ≤ U^B := by
    calc
      T ≤ Real.exp (b*X) := hTU
      _ ≤ Real.exp (d*X*B) := by
        apply Real.exp_le_exp.mpr
        have hdb : d*B = d+b := by dsimp [B]; field_simp
        rw [mul_assoc, mul_comm X B, ← mul_assoc, hdb]
        nlinarith
      _ = (Real.exp (d*X))^B := Real.exp_mul _ _
      _ ≤ U^B := Real.rpow_le_rpow (Real.exp_pos _).le hU (by linarith)
  have hsmall : (S.card:ℝ)*U^(1-η) ≤ U := habsorb U S.card hU hcard
  have hrow : ∀ t ∈ S, ∑ u ∈ S, ‖markedLogKernel L R (t-u)‖ ≤
      A*U*(3+2*Real.log (T+1)) := by
    intro t ht
    apply (hU₀ U (hXU₀.trans hU) L R S T hL hR hT hTpower hsep hdiam t ht).trans
    calc
      _ ≤ A*(2*U*(1+Real.log (T+1))+U) :=
        mul_le_mul_of_nonneg_left (by linarith) hA.le
      _ = _ := by ring
  have hlogT : Real.log (T+1) ≤ Real.log 2+b*X := by
    have hexp : 1 ≤ Real.exp (b*X) := Real.one_le_exp_iff.mpr hbX
    calc
      Real.log (T+1) ≤ Real.log (2*Real.exp (b*X)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
  have hlogscale : 3+2*Real.log (T+1) ≤ (3+2*Real.log 2+2*b)*X := by
    have hc := mul_le_mul_of_nonneg_left hX (show 0 ≤ 3+2*Real.log 2 by positivity)
    nlinarith
  have hlog0 : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  calc
    _ ≤ (A*U*(3+2*Real.log (T+1))) * (∑ n ∈ Finset.Icc L R, ‖a n / U‖^2) :=
      markedDyadicPolynomial_sparse_energy L R U a S (by positivity) hrow
    _ ≤ A*U*((3+2*Real.log 2+2*b)*X) * (∑ n ∈ Finset.Icc L R, ‖a n / U‖^2) := by
      gcongr
    _ = _ := by dsimp [K]; ring

/-- The squared coefficient mass controls the actual suprema on sparse
closed unit intervals. No pointwise coefficient cap is required. -/
theorem sourceComparisonSparse_unitInterval_energy
    (d b C Q : ℝ) (hd : 0 < d) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (U T : ℝ) (L R : ℕ) (a : ℕ → ℂ) (I : Finset ℤ),
        Real.exp (d*X) ≤ U → 1 ≤ T → T ≤ Real.exp (b*X) →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        (I.card:ℝ) ≤ Q*Real.exp (C*X^(91/(100:ℝ))) →
        (∀ z ∈ I, ∃ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1), |t| ≤ T) →
        (∑ z ∈ I, sSup ((fun t => ‖markedDyadicPolynomial L R U a t‖^2) ''
          Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤
          K*X*U*(∑ n ∈ Finset.Icc L R, ‖a n / U‖^2) := by
  obtain ⟨K, hK, henergy⟩ := sourceComparisonSparse_sample_energy d (b+1) C Q hd
    (by positivity)
  refine ⟨3*K, by positivity, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (Real.log 4)] with X henergy hX
  intro U T L R a I hU hT hTU hL hR hI hwitness
  have hheight : 2*(T+1) ≤ Real.exp ((b+1)*X) := by
    calc
      2*(T+1) ≤ 4*T := by linarith
      _ ≤ 4*Real.exp (b*X) := mul_le_mul_of_nonneg_left hTU (by norm_num)
      _ = Real.exp (Real.log 4+b*X) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hclosure : ∀ z ∈ I, ∀ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1), |t| ≤ T+1 := by
    intro z hz t ht
    obtain ⟨w, hw, hwT⟩ := hwitness z hz
    exact unitInterval_abs_bound_of_witness ht hw hwT
  have hsamples : ∀ S : Finset ℝ, S.card ≤ I.card →
      (∀ t ∈ S, |t| ≤ T+1) →
      (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ S, ‖markedDyadicPolynomial L R U a t‖^2) ≤
        K*X*U*(∑ n ∈ Finset.Icc L R, ‖a n / U‖^2) := by
    intro S hSI hS hsep
    have hcardS : (S.card:ℝ) ≤ Q*Real.exp (C*X^(91/(100:ℝ))) :=
      (show (S.card:ℝ) ≤ I.card by exact_mod_cast hSI).trans hI
    apply henergy U (2*(T+1)) L R S a hU (by linarith) hheight hL hR hcardS hsep
    intro t ht u hu
    linarith [abs_sub t u, hS t ht, hS u hu]
  calc
    _ ≤ 3*(K*X*U*(∑ n ∈ Finset.Icc L R, ‖a n / U‖^2)) :=
      unitInterval_sum_sup_le I (fun t => |t| ≤ T+1)
        (fun t => ‖markedDyadicPolynomial L R U a t‖^2)
        (markedDyadicPolynomial_norm_sq_continuous L R U a) hclosure hsamples
    _ = _ := by ring

end
end ArtinMatthews
