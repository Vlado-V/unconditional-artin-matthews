module

public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.MarkedProgressionGrowth
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

/-! The complete dilation contains exactly the copied and auxiliary
slots of each original group. Its actual bound is uniform in the free
pattern and in all label values. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

def giantTwoSidedPatternDilation {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell : ℕ} (C : J → Finset (Fin k)) (labels : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P C) : ℕ :=
  giantTwoSidedPatternCopiedProduct C labels*giantTwoSidedPatternAuxiliaryProduct aux

theorem giantTwoSidedPatternDilation_pos {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {k ell : ℕ} (C : J → Finset (Fin k))
    (labels : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    0 < giantTwoSidedPatternDilation C labels aux :=
  Nat.mul_pos (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (labels j (Fin.castAdd ell i)).property).pos)
    (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (aux j i).property).pos)

theorem giantTwoSidedPatternDilation_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} (C : J → Finset (Fin k))
    (labels : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C)
    {Y : ℝ} (hY : 0 ≤ Y) (hP : ∀ j p,p∈P j → (p:ℝ)≤Y) :
    (giantTwoSidedPatternDilation C labels aux:ℝ) ≤ Y^(k*Fintype.card J) := by
  have hc (j : J) : (C j).card≤k := by
    simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (C j))
  have hcop (j : J) : (∏ i∈univ \ C j,(labels j (Fin.castAdd ell i):ℝ)) ≤ Y^(k-(C j).card) := by
    calc
      _ ≤ ∏ _i∈univ \ C j,Y := prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => hP j _ (labels j (Fin.castAdd ell i)).property)
      _ = _ := by rw [prod_const,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
  have haux (j : J) : (∏ i : ↥(C j),(aux j i:ℝ)) ≤ Y^(C j).card := by
    calc
      _ ≤ ∏ _i : ↥(C j),Y := prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => hP j _ (aux j i).property)
      _ = _ := by rw [prod_const,card_univ,Fintype.card_coe]
  have hprod : (∏ j,(∏ i∈univ \ C j,(labels j (Fin.castAdd ell i):ℝ))*
      (∏ i : ↥(C j),(aux j i:ℝ))) ≤ ∏ j,Y^(k-(C j).card)*Y^(C j).card := by
    apply prod_le_prod₀ (fun _ _ => mul_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _)
      (prod_nonneg fun _ _ => Nat.cast_nonneg _))
    intro j _
    exact mul_le_mul (hcop j) (haux j) (prod_nonneg fun _ _ => Nat.cast_nonneg _) (pow_nonneg hY _)
  calc
    _ = ∏ j,(∏ i∈univ \ C j,(labels j (Fin.castAdd ell i):ℝ))*
      (∏ i : ↥(C j),(aux j i:ℝ)) := by
        simp only [giantTwoSidedPatternDilation,giantTwoSidedPatternCopiedProduct,
          giantTwoSidedPatternAuxiliaryProduct,Nat.cast_mul,Nat.cast_prod,prod_mul_distrib]
    _ ≤ _ := hprod
    _ = Y^(k*Fintype.card J) := by
      simp_rw [← pow_add,Nat.sub_add_cancel (hc _)]
      rw [prod_const,card_univ,← pow_mul,Nat.mul_comm]

theorem giantCandidatePatternDilation_exp_bound (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (ell : ℕ) (C : S → Finset (Fin k)) (labels : MarkedPhysicalMarking P (k+ell))
        (aux : GiantTwoSidedPatternAuxiliary P C),
        (giantTwoSidedPatternDilation C labels aux:ℝ) ≤
          Real.exp (((k:ℝ)*giantCandidateGroupLogRate)*(Real.log x)^(46/100:ℝ)) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/100)).bound (zero_lt_one : (0:ℝ)<1)
  filter_upwards [giantCandidateGroup_total_count_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually hlog]
    with x hcount hx hL hlog
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let L := Real.log x
  dsimp only
  intro ell C labels aux
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hg : (S.card:ℝ) ≤ giantCandidateGroupLogRate*Real.log L :=
    (Nat.cast_le.mpr (card_le_univ S)).trans hcount
  have hp (i : S) (p : ℕ) (hp : p∈P i) : (p:ℝ)≤Real.exp (L^(45/100:ℝ)) :=
    (giantCandidateFullPrimes_range hx hL (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).2.2.le
  have hlog' : Real.log L ≤ L^(1/100:ℝ) := by
    change ‖Real.log L‖ ≤ 1*‖L^(1/100:ℝ)‖ at hlog
    simp only [Real.norm_eq_abs,one_mul] at hlog
    rw [abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
    exact (le_abs_self _).trans hlog
  have hrate : 0≤giantCandidateGroupLogRate := by unfold giantCandidateGroupLogRate; positivity
  calc
    _ ≤ (Real.exp (L^(45/100:ℝ)))^(k*Fintype.card S) :=
      giantTwoSidedPatternDilation_le C labels aux (Real.exp_nonneg _) hp
    _ = Real.exp ((k:ℝ)*(S.card:ℝ)*L^(45/100:ℝ)) := by
      rw [← Real.exp_nat_mul,Nat.cast_mul,Fintype.card_coe]
    _ ≤ Real.exp (((k:ℝ)*giantCandidateGroupLogRate)*(L^(1/100:ℝ)*L^(45/100:ℝ))) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _))
        (Real.rpow_nonneg hL0.le _)).trans (by
          nlinarith only [mul_le_mul_of_nonneg_left hlog'
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hrate) (Real.rpow_nonneg hL0.le (45/100:ℝ)))])
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num [L]

theorem giantCandidatePatternDilation_subpower (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (ell : ℕ) (C : S → Finset (Fin k)) (labels : MarkedPhysicalMarking P (k+ell))
        (aux : GiantTwoSidedPatternAuxiliary P C), (giantTwoSidedPatternDilation C labels aux:ℝ) ≤ x^δ := by
  filter_upwards [giantCandidatePatternDilation_exp_bound k,
    marked_sublinear_log_exp_le_rpow_eventually (46/100) ((k:ℝ)*giantCandidateGroupLogRate) δ
      (by norm_num) hδ] with x hD hg
  intro S
  dsimp only
  intro ell C labels aux
  exact (hD S ell C labels aux).trans hg

end
end ArtinMatthews
