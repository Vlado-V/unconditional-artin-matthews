module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.EgyptianFractions.CorrelationPhase
public import OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseScale
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseSecondDerivative
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseTerminalBudget


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! # Uniform terminal cancellation for logarithmic phases -/
namespace JointDickman
open Problem337

lemma logarithmic_terminal_scale_eq (hs : List ℝ) {k : ℕ}
    (hlen : hs.length+1=k) {U : ℝ} (hU : 0 < U) (Z : ℝ) :
    hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2) =
      ((k.factorial:ℝ)/(4:ℝ)^(k+1))*(|Z| *U^(-((k:ℝ)+1))*hs.prod) := by
  have hpow : U^(-((k:ℝ)+1)) = (U^(k+1))⁻¹ := by
    rw [Real.rpow_neg hU.le]
    congr 1
    norm_cast
  rw [hlen,show hs.length+2=k+1 by omega,mul_pow,hpow]
  ring

/-- The last differenced sums have a fixed power saving. The hypotheses are
only scalar size relations for the actual logarithmic phase. -/
theorem logarithmic_terminal_range_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U Z x : ℝ) (N : ℕ) (hs : List ℝ),
      2 ≤ U → hs.length+1=k →
      (∀ h ∈ hs, 1 ≤ h ∧ h ≤ U^(1/(10*(k:ℝ)))) →
      U^(-(3:ℝ)/2) ≤ |Z| *U^(-((k:ℝ)+1)) →
      |Z| *U^(-((k:ℝ)+1)) ≤ U^(-(1:ℝ)/2) →
      U ≤ x → x+(N:ℝ)+hs.sum ≤ 4*U → (N:ℝ) ≤ 3*U →
      ‖∑ j ∈ Finset.range N, ExponentialSum.phase
        (forwardDifference hs (fun y => a*y+Z*Real.log y) ((j:ℝ)+x))‖ ≤
        C*U^((4:ℝ)/5) := by
  let c : ℝ := (k.factorial:ℝ)/(4:ℝ)^(k+1)
  let A : ℝ := (4:ℝ)^(k+1)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(6*A+15)*(3*(c^((1:ℝ)/2)+c^(-(1:ℝ)/2)+1)),by positivity,?_⟩
  intro a U Z x N hs hU hlen hhs hlo hhi hx hend hN
  have hU0 : 0 < U := by linarith
  have hpos : ∀ h ∈ hs, 0 < h := fun h hh => by linarith [(hhs h hh).1]
  have hZ : Z ≠ 0 := by
    intro h
    rw [h,abs_zero,zero_mul] at hlo
    exact (not_le_of_gt (Real.rpow_pos_of_pos hU0 _)) hlo
  have hraw := logarithmic_difference_sum_bound hs hpos a Z U x N hZ hU0 hx hend
  dsimp only at hraw
  rw [logarithmic_terminal_scale_eq hs hlen hU0 Z,
    show hs.length+2=k+1 by omega] at hraw
  obtain ⟨hlow,hhigh⟩ := logarithmic_phase_shift_scale (by linarith : 1<U) hk
    hlo hhi hs (by omega) hhs
  have hb := logarithmic_terminal_sqrt_budget (by linarith : 1≤U) hc hN
    (mul_le_mul_of_nonneg_left hlow hc.le)
    (mul_le_mul_of_nonneg_left hhigh hc.le)
  apply hraw.trans
  change (6*A+15)*_ ≤ _
  calc
    _ ≤ (6*A+15)*(3*(c^((1:ℝ)/2)+c^(-(1:ℝ)/2)+1)*U^((4:ℝ)/5)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem logarithmic_terminal_interval_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U Z : ℝ) (L R : ℤ) (hs : List ℤ),
      2 ≤ U → hs.length = k - 1 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => a*y+Z*Real.log y) n)‖ ≤ C * U ^ ((4 : ℝ) / 5) := by
  obtain ⟨C, hC, hbound⟩ := logarithmic_terminal_range_bound k hk
  refine ⟨C, hC, ?_⟩
  intro a U Z L R hs hU hlen hhs hlo hhi hL hR
  have hU0 : 0 < U := by linarith
  have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (hhs h hh).1.le)
  by_cases hempty : R - hs.sum < L
  · rw [Finset.Icc_eq_empty (not_le_of_gt hempty), Finset.sum_empty, norm_zero]
    positivity
  have hne : L ≤ R - hs.sum := by omega
  let N := (R - hs.sum + 1 - L).toNat
  have hNi : (N : ℤ) = R - hs.sum + 1 - L := Int.toNat_of_nonneg (by omega)
  have hNr := congrArg (fun n : ℤ => (n : ℝ)) hNi
  push_cast at hNr
  have hsumR : ((hs.map (fun h : ℤ => (h : ℝ))).sum) = (hs.sum : ℝ) := by
    simp
  have hspos : (0 : ℝ) ≤ (hs.sum : ℝ) := by exact_mod_cast hsum
  have hh := hbound a U Z L N (hs.map (fun h : ℤ => (h : ℝ))) hU
    (by simp only [List.length_map, hlen]; omega)
    (by
      intro h hh
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
      constructor
      · exact_mod_cast (show (1 : ℤ) ≤ j by have := (hhs j hj).1; omega)
      · have hh : (j : ℝ) < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℝ) := by
          exact_mod_cast (hhs j hj).2
        exact hh.le.trans (Nat.floor_le (Real.rpow_nonneg hU0.le _)))
    hlo hhi hL
    (by rw [hsumR]; linarith)
    (by linarith)
  have heq : (∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => a*y+Z*Real.log y) n)) =
      ∑ j ∈ Finset.range N,
        ExponentialSum.phase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => a*y+Z*Real.log y) ((j : ℝ) + L)) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
    rw [add_comm]
    rfl
  rwa [heq]


end JointDickman

end OAI
