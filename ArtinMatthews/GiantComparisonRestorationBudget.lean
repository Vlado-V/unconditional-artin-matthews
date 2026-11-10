module

public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantComparisonSharedLoss
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The scale in the two fourth moments cancels the inverse square
root in the row estimate. Only a fixed logarithmic power remains. -/
namespace ArtinMatthews
open Finset Filter Set
open scoped BigOperators Topology
noncomputable section

theorem giantComparisonFourthFactors_le {C Y L D U V : ℝ}
    (hC : 0 < C) (hY : 0 < Y) (hL : 0 < L)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hU : U ≤ C*Y*L^D) (hV : V ≤ C*Y*L^D) :
    Y^(-(1/2:ℝ))*U^(1/4:ℝ)*V^(1/4:ℝ) ≤ C^(1/2:ℝ)*L^(D/2) := by
  let M := C*Y*L^D
  have hM : 0 < M := mul_pos (mul_pos hC hY) (Real.rpow_pos_of_pos hL _)
  have hYinv : Y^(-(1/2:ℝ))*Y^(1/2:ℝ) = 1 := by
    rw [← Real.rpow_add hY]
    norm_num
  have hpower : M^(1/4:ℝ)*M^(1/4:ℝ) = C^(1/2:ℝ)*Y^(1/2:ℝ)*L^(D/2) := calc
    _ = M^(1/2:ℝ) := by rw [← Real.rpow_add hM]; norm_num
    _ = _ := by
      dsimp only [M]
      rw [Real.mul_rpow (mul_nonneg hC.le hY.le) (Real.rpow_nonneg hL.le _),
        Real.mul_rpow hC.le hY.le,← Real.rpow_mul hL.le]
      congr 1
      ring
  calc
    _ ≤ Y^(-(1/2:ℝ))*M^(1/4:ℝ)*M^(1/4:ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hU0 hU (by norm_num))
        (Real.rpow_nonneg hY.le _)) (Real.rpow_le_rpow hV0 hV (by norm_num))
        (Real.rpow_nonneg hV0 _) (by positivity)
    _ = (Y^(-(1/2:ℝ))*Y^(1/2:ℝ))*(C^(1/2:ℝ)*L^(D/2)) := by
      rw [mul_assoc,hpower]
      ring
    _ = _ := by rw [hYinv,one_mul]

theorem giantCandidateComparisonAuxiliarySlots_log_bound (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x))
      (C : S → Finset (Fin k)),
      (Fintype.card (Σ g : S, ↥(C g)):ℝ) ≤ ((k:ℝ)*giantCandidateGroupLogRate)*Real.log x := by
  filter_upwards [giantCandidateGroup_total_count_eventually,
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hgroup hlog
  intro S C
  have hrate : 0 ≤ giantCandidateGroupLogRate := by unfold giantCandidateGroupLogRate; positivity
  have hS : (S.card:ℝ) ≤ giantCandidateGroupLogRate*Real.log (Real.log x) :=
    (Nat.cast_le.mpr (Finset.card_le_univ S)).trans hgroup
  have hL : Real.log (Real.log x) ≤ Real.log x :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlog)).trans (by linarith)
  calc
    _ ≤ (k:ℝ)*(S.card:ℝ) := by
      have h := giantComparisonAuxiliarySlots_card_le C
      rw [Fintype.card_coe] at h
      exact_mod_cast h
    _ ≤ (k:ℝ)*(giantCandidateGroupLogRate*Real.log (Real.log x)) :=
      mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
    _ ≤ (k:ℝ)*(giantCandidateGroupLogRate*Real.log x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hrate) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem giantComparisonRestorationLogBudget_eventually (A D C K : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      C*(Real.log x)^D*
          ((Real.log x)^(-(A+D))+
            K*Real.log x*Real.exp (-(Real.log x)^(39/100:ℝ)/2)) ≤
        (C+1)*(Real.log x)^(-A) := by
  have ht := ((rpow_mul_exp_neg_rpow_tendsto (D+1+A) (δ:=39/100) (b:=1/2)
    (by norm_num) (by norm_num)).comp Real.tendsto_log_atTop).const_mul (C*K)
  simp only [Function.comp_def,mul_zero] at ht
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    ht.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))] with x hlog hsmall
  let L := Real.log x
  let E := Real.exp (-(L^(39/100:ℝ))/2)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hs : C*K*(L^(D+1+A)*E) ≤ 1 := by
    change C*K*(L^(D+1+A)*Real.exp (-(1/2:ℝ)*L^(39/100:ℝ))) < 1 at hsmall
    simpa only [E,show -(1/2:ℝ)*L^(39/100:ℝ)=-(L^(39/100:ℝ))/2 by ring] using hsmall.le
  have hp : L^(D+1+A)*L^(-A) = L^D*L := by
    rw [← Real.rpow_add hL,show D+1+A+(-A)=D+1 by ring,Real.rpow_add hL,Real.rpow_one]
  have hfirst : L^D*L^(-(A+D)) = L^(-A) := by
    rw [← Real.rpow_add hL,show D+(-(A+D)) = -A by ring]
  change C*L^D*(L^(-(A+D))+K*L*E) ≤ (C+1)*L^(-A)
  calc
    _ = C*(L^D*L^(-(A+D)))+(C*K*E)*(L^D*L) := by ring
    _ = C*L^(-A)+(C*K*(L^(D+1+A)*E))*L^(-A) := by rw [hfirst,← hp]; ring
    _ ≤ C*L^(-A)+1*L^(-A) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hL.le _))
    _ = _ := by ring

end
end ArtinMatthews
