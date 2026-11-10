module

public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantCandidateAllocationWeights
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal active one-mark factors have uniform fixed log-power
growth, including when the selected families grow with the scale. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantCandidateOneMarkBound (q : ℝ) : ℝ :=
  (2/Real.log 2)/(1-q)

theorem giantCandidateOneMarkBound_one_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 ≤ giantCandidateOneMarkBound q := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : (1:ℝ) ≤ 2/Real.log 2 := (le_div_iff₀ hlog0).mpr (by linarith)
  exact (le_div_iff₀ (sub_pos.mpr hq1)).mpr (by linarith [h2])

theorem giantCandidateOneMarkFactor_le {q V : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hV : Real.log 2/2 ≤ V) (k : ℕ) :
    (k:ℝ)/V * q^(k-1) ≤ giantCandidateOneMarkBound q := by
  have hV0 : 0 < V := (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans_le hV
  have hB : 0 ≤ giantCandidateOneMarkBound q :=
    zero_le_one.trans (giantCandidateOneMarkBound_one_le hq0 hq1)
  cases k with
  | zero => simpa only [Nat.cast_zero,zero_div,zero_mul] using hB
  | succ k =>
    have hsum : (k.succ:ℝ)*q^k ≤ ∑ r ∈ range k.succ,q^r := by
      calc
        _ = ∑ _r ∈ range k.succ,q^k := by simp only [sum_const,nsmul_eq_mul,card_range]
        _ ≤ _ := by
          apply sum_le_sum
          intro r hr
          exact pow_le_pow_of_le_one hq0 hq1.le (Nat.le_of_lt_succ (mem_range.mp hr))
    have hgeo : (∑ r ∈ range k.succ,q^r) ≤ 1/(1-q) := by
      apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
      rw [geom_sum_mul_neg]
      exact sub_le_self _ (pow_nonneg hq0 _)
    have hinv : 1/V ≤ 2/Real.log 2 := by
      have h := one_div_le_one_div_of_le (div_pos (Real.log_pos (by norm_num)) (by norm_num)) hV
      exact h.trans_eq (by ring)
    rw [Nat.succ_sub_one]
    calc
      _ = ((k.succ:ℝ)*q^k)*(1/V) := by ring
      _ ≤ (1/(1-q))*(2/Real.log 2) :=
        mul_le_mul (hsum.trans hgeo) hinv (by positivity) (by positivity)
      _ = _ := by unfold giantCandidateOneMarkBound; ring

theorem giantCandidateActiveOneMark_nonneg {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ giantCandidateActiveOneMark P q n := by
  unfold giantCandidateActiveOneMark
  apply prod_nonneg
  intro i _
  have hV : 0 ≤ bandReciprocalMass (P i) := sum_nonneg (fun _ _ => by positivity)
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hV) (pow_nonneg hq _)

theorem giantCandidateActiveOneMark_actual_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (n : ℕ),
      ‖(giantCandidateActiveOneMark (fun i : S => giantCandidateGroup x i.val) q n:ℂ)‖ ≤
        (Real.log x)^(giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound q)) := by
  let B := giantCandidateOneMarkBound q
  filter_upwards [giantCandidateGroup_mass_eventually,
    giantCandidateSelectedGroups_exponential_cost_eventually B (giantCandidateOneMarkBound_one_le hq0 hq1)]
    with x hmass hcost
  intro S n
  let P (i : S) := giantCandidateGroup x i.val
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (giantCandidateActiveOneMark_nonneg P hq0 n)]
  apply le_trans _ (hcost S)
  unfold giantCandidateActiveOneMark
  have hprod := Finset.prod_le_prod₀ (s:=(univ : Finset S))
    (f:=fun i => (bandCount (P i) n:ℝ)/bandReciprocalMass (P i)*q^(bandCount (P i) n-1))
    (g:=fun _ => B)
    (fun i _ => by
      have hV : 0 ≤ bandReciprocalMass (P i) := sum_nonneg (fun _ _ => by positivity)
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hV) (pow_nonneg hq0 _))
    (fun i _ => giantCandidateOneMarkFactor_le hq0 hq1 (hmass i.val).1.le _)
  simpa only [prod_const,card_univ,Fintype.card_coe] using hprod

end
end ArtinMatthews
