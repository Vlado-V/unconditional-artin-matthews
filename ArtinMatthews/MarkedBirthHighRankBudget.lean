module

public import ArtinMatthews.MarkedBirthRankCutoff
public import ArtinMatthews.MarkedBirthAddressBudget
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

/-! The actual high-rank numerical margin. One prescribed atom per
cycle nonpivot absorbs the proved coarse permutation count and every
fixed polynomial cost per operation at the literal moment length. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedBirth_high_rank_term_budget (K : ℕ) (P G cutoffScale : ℝ)
    (hP : 0 ≤ P) (hScale : 2*(2*P+G+2) ≤ cutoffScale) :
    ∀ᶠ x : ℝ in atTop, ∀ r : ℕ, markedBirthRankCutoff cutoffScale x ≤ r →
      ((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^(2*r)*
        ((Real.log x)^P)^(markedMemoryMomentLength x+1)*
        (markedMemoryBirthAtomEnvelope x)^r ≤
      ((Real.log x)^(-(G+2)))^(markedMemoryMomentLength x) := by
  filter_upwards [markedMemoryBirth_rank_ratio_eventually K,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hratio hlog
  intro r hr
  let L := Real.log x
  let N := markedMemoryMomentLength x
  let a := L^(1/10:ℝ)
  have hL₁ : 1 ≤ L := hlog
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have ha : 0 < a := Real.rpow_pos_of_pos hL _
  have hN₁ : 1 ≤ (N:ℝ) :=
    (Real.one_le_rpow hL₁ (by norm_num : (0:ℝ) ≤ 1/2)).trans (markedMemoryMomentLength_lower hL.le)
  have hr' : cutoffScale*(N:ℝ)*Real.log L/a ≤ (r:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hr)
  have hpay : cutoffScale*(N:ℝ)*Real.log L ≤ (r:ℝ)*a :=
    (div_le_iff₀ ha).mp hr'
  have hexp : Real.exp ((r:ℝ)*(-a/2)) ≤
      Real.exp (Real.log L*(-cutoffScale/2*(N:ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hpay]
  have hpow : (((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^2*
      markedMemoryBirthAtomEnvelope x)^r ≤ (Real.exp (-a/2))^r :=
    pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (markedMemoryBirthAtomEnvelope_pos x).le) hratio r
  have he : P*((N:ℝ)+1)-cutoffScale/2*(N:ℝ) ≤ -(G+2)*(N:ℝ) := by
    have hPN : P ≤ P*(N:ℝ) := by nlinarith
    have hS := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))
    nlinarith
  calc
    _ = ((L^P)^(N+1))*
        ((((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^2)*markedMemoryBirthAtomEnvelope x)^r := by
      rw [mul_pow,pow_mul]
      ring
    _ ≤ ((L^P)^(N+1))*(Real.exp (-a/2))^r :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg (Real.rpow_nonneg hL.le _) _)
    _ = ((L^P)^(N+1))*Real.exp ((r:ℝ)*(-a/2)) := by rw [Real.exp_nat_mul]
    _ ≤ ((L^P)^(N+1))*Real.exp (Real.log L*(-cutoffScale/2*(N:ℝ))) :=
      mul_le_mul_of_nonneg_left hexp (pow_nonneg (Real.rpow_nonneg hL.le _) _)
    _ = L^(P*((N:ℝ)+1)-cutoffScale/2*(N:ℝ)) := by
      rw [← Real.rpow_def_of_pos hL,← Real.rpow_mul_natCast hL.le,← Real.rpow_add hL]
      congr 1
      push_cast
      ring
    _ ≤ L^(-(G+2)*(N:ℝ)) := Real.rpow_le_rpow_of_exponent_le hL₁ he
    _ = _ := by rw [Real.rpow_mul_natCast hL.le]

end ArtinMatthews
