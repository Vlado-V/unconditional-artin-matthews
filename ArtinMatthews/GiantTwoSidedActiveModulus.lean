module

public import ArtinMatthews.GiantTwoSidedLabelOffsets
public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
public import ArtinMatthews.MarkedPhysicalPathUsedBudget
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

/-! The forced modulus is the product of the distinct primes active
somewhere on the literal ordered label path. Its actual budget includes
all visits and all marks while counting each used prime once. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantTwoSidedActiveModulus {J : Type*} [Fintype J] {P : J → Finset ℕ} {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) : ℕ :=
  ∏ p∈markedPhysicalPathUsedPrimes univ labels,p

theorem giantTwoSidedActiveModulus_pos {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) : 0<giantTwoSidedActiveModulus labels := by
  apply prod_pos
  intro p hp
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp (markedPhysicalPathUsedPrimes_subset univ labels hp)
  exact (hP j p hj).pos

theorem giantTwoSidedActiveModulus_coprime {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M n p : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (hp : p.Prime)
    (hout : p∉markedPhysicalPathUsedPrimes univ labels) : p.Coprime (giantTwoSidedActiveModulus labels) := by
  apply Nat.Coprime.prod_right
  intro q hq
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp (markedPhysicalPathUsedPrimes_subset univ labels hq)
  exact (Nat.coprime_primes hp (hP j q hj)).mpr (fun he => hout (he ▸ hq))

theorem giantCandidateActiveModulus_bound (M : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ labels : Fin (n+1) → MarkedPhysicalMarking P M,
        (giantTwoSidedActiveModulus labels:ℝ) ≤
          Real.exp ((5*(M:ℝ)*giantCandidateGroupLogRate)*(Real.log x)^(49/50:ℝ)) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/100)).bound (zero_lt_one : (0:ℝ)<1)
  filter_upwards [giantCandidateGroup_total_count_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually hlog]
    with x hcount hx hL hlog
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  dsimp only
  intro labels
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hrate : 0≤giantCandidateGroupLogRate := by unfold giantCandidateGroupLogRate; positivity
  have hlog' : Real.log L ≤ L^(1/100:ℝ) := by
    change ‖Real.log L‖ ≤ 1*‖L^(1/100:ℝ)‖ at hlog
    simp only [Real.norm_eq_abs,one_mul] at hlog
    rw [abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
    exact (le_abs_self _).trans hlog
  have hg : (Fintype.card S:ℝ) ≤ giantCandidateGroupLogRate*L^(1/100:ℝ) := by
    rw [Fintype.card_coe]
    exact ((Nat.cast_le.mpr (card_le_univ S)).trans hcount).trans
      (mul_le_mul_of_nonneg_left hlog' hrate)
  have hv : ((n+1:ℕ):ℝ) ≤ 5*L^(13/25:ℝ) := by
    rw [Nat.cast_add,Nat.cast_one]
    have hn := giantTwoSidedSourceMomentLength_le hL
    have hy := Real.one_le_rpow hL (by norm_num : (0:ℝ)≤13/25)
    linarith
  have hp (i : S) (p : ℕ) (hp : p∈P i) : (p:ℝ)≤Real.exp (L^(45/100:ℝ)) :=
    (giantCandidateFullPrimes_range hx hL (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).2.2.le
  calc
    _ ≤ Real.exp (((n+1:ℕ):ℝ)*(Fintype.card S:ℝ)*(M:ℝ)*L^(45/100:ℝ)) := by
      simpa only [giantTwoSidedActiveModulus,Nat.cast_prod,card_univ,Fintype.card_fin] using
        markedPhysicalPathUsedPrimes_prod_le_exp (univ : Finset (Fin (n+1))) labels
          (L^(45/100:ℝ)) (Real.rpow_nonneg hL0.le _) hp
    _ ≤ Real.exp ((5*L^(13/25:ℝ))*(giantCandidateGroupLogRate*L^(1/100:ℝ))*(M:ℝ)*L^(45/100:ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul hv hg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg M))
        (Real.rpow_nonneg hL0.le _)
    _ = _ := by
      congr 1
      rw [show (49/50:ℝ)=13/25+1/100+45/100 by norm_num,Real.rpow_add hL0,Real.rpow_add hL0]
      ring

end
end ArtinMatthews
