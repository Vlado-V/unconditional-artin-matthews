module

public import ArtinMatthews.MarkedPhysicalMarking
public import ArtinMatthews.GiantTwoSidedLabelOffsets
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Literal independent product-label probability and coordinate
averaging, including repetitions and arbitrary full-tuple tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealLabelMass {J : Type*} [Fintype J] (P : J → Finset ℕ) (M : ℕ)
    (a : MarkedPhysicalMarking P M) : ℝ :=
  ∏ j,∏ i,markedHarmonicAtom (P j) (a j i)

theorem idealLabelMass_nonneg {J : Type*} [Fintype J] (P : J → Finset ℕ) (M : ℕ)
    (hV : ∀ j,0 < bandReciprocalMass (P j)) (a : MarkedPhysicalMarking P M) :
    0 ≤ idealLabelMass P M a :=
  prod_nonneg fun j _ => prod_nonneg fun _ _ => markedHarmonicAtom_nonneg (P j) (hV j)

theorem idealLabelMass_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (hV : ∀ j,0 < bandReciprocalMass (P j)) :
    (∑ a : MarkedPhysicalMarking P M,idealLabelMass P M a)=1 := by
  unfold idealLabelMass
  simp_rw [← markedPhysicalMass_mul_reciprocal]
  exact markedPhysicalMarking_normalized_sum P M hV

def idealLabelEnergy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (f : MarkedPhysicalMarking P M → ℂ) : ℝ :=
  ∑ a,idealLabelMass P M a*‖f a‖^2

def idealMix {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (S : Finset (J × Fin M)) (a b : MarkedPhysicalMarking P M) : MarkedPhysicalMarking P M :=
  fun j i => if (j,i)∈S then b j i else a j i

def idealMixEquiv {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (S : Finset (J × Fin M)) :
    (MarkedPhysicalMarking P M × MarkedPhysicalMarking P M) ≃
      (MarkedPhysicalMarking P M × MarkedPhysicalMarking P M) where
  toFun z := (idealMix S z.1 z.2,idealMix S z.2 z.1)
  invFun z := (idealMix S z.1 z.2,idealMix S z.2 z.1)
  left_inv z := by
    apply Prod.ext <;> funext j i <;> simp only [idealMix] <;> split_ifs <;> rfl
  right_inv z := by
    apply Prod.ext <;> funext j i <;> simp only [idealMix] <;> split_ifs <;> rfl

theorem idealLabelMass_mix {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (S : Finset (J × Fin M)) (a b : MarkedPhysicalMarking P M) :
    idealLabelMass P M (idealMix S a b)*idealLabelMass P M (idealMix S b a)=
      idealLabelMass P M a*idealLabelMass P M b := by
  unfold idealLabelMass
  rw [← prod_mul_distrib,← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  rw [← prod_mul_distrib,← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  unfold idealMix
  split_ifs
  · exact mul_comm _ _
  · rfl

def idealLabelExpectation {J A : Type*} [Fintype J] [DecidableEq J]
    [CommRing A] [Algebra ℝ A] (P : J → Finset ℕ) (M : ℕ)
    (f : MarkedPhysicalMarking P M → A) : A :=
  ∑ a,algebraMap ℝ A (idealLabelMass P M a)*f a

theorem idealLabelExpectation_mix {J A : Type*} [Fintype J] [DecidableEq J]
    [CommRing A] [Algebra ℝ A] (P : J → Finset ℕ) (M : ℕ)
    (hV : ∀ j,0 < bandReciprocalMass (P j)) (S : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → A) :
    idealLabelExpectation P M (fun a => idealLabelExpectation P M (fun b => f (idealMix S a b)))=
      idealLabelExpectation P M f := by
  have he := (idealMixEquiv (P:=P) S).sum_comp
    (fun z : MarkedPhysicalMarking P M × MarkedPhysicalMarking P M =>
      algebraMap ℝ A (idealLabelMass P M z.1*idealLabelMass P M z.2)*f z.1)
  simp only [idealMixEquiv,Equiv.coe_fn_mk,idealLabelMass_mix] at he
  unfold idealLabelExpectation
  simp only [mul_sum,← mul_assoc,← map_mul]
  rw [Fintype.sum_prod_type] at he
  rw [he]
  rw [Fintype.sum_prod_type]
  have hm : (∑ a : MarkedPhysicalMarking P M,algebraMap ℝ A (idealLabelMass P M a))=1 := by
    rw [← map_sum,idealLabelMass_sum P M hV,map_one]
  apply sum_congr rfl
  intro a _
  calc
    _ = (algebraMap ℝ A (idealLabelMass P M a)*f a)*
        ∑ b : MarkedPhysicalMarking P M,algebraMap ℝ A (idealLabelMass P M b) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      rw [map_mul]
      ring
    _ = _ := by rw [hm,mul_one]

def idealAverageSet {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (S : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) (a : MarkedPhysicalMarking P M) : ℂ :=
  idealLabelExpectation P M (fun b => f (idealMix S a b))

theorem idealAverageSet_idempotent {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (S : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealAverageSet P S (idealAverageSet P S f)=idealAverageSet P S f := by
  funext a
  have hm : (∑ b : MarkedPhysicalMarking P M,algebraMap ℝ ℂ (idealLabelMass P M b))=1 := by
    rw [← map_sum,idealLabelMass_sum P M hV,map_one]
  unfold idealAverageSet idealLabelExpectation
  have hmix (b c : MarkedPhysicalMarking P M) : idealMix S (idealMix S a b) c=idealMix S a c := by
    funext j i
    simp only [idealMix]
    split_ifs <;> rfl
  simp_rw [hmix]
  rw [← sum_mul,hm,one_mul]

theorem idealWeightedJensen {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i,0 ≤ w i) (hm : ∑ i,w i=1) (f : ι → ℂ) :
    ‖∑ i,(w i:ℂ)*f i‖^2 ≤ ∑ i,w i*‖f i‖^2 := by
  have hn : ‖∑ i,(w i:ℂ)*f i‖ ≤ ∑ i,w i*‖f i‖ := by
    refine (norm_sum_le _ _).trans_eq ?_
    apply sum_congr rfl
    intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw i)]
  have hs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (fun i _ => hw i)
    (fun i _ => mul_nonneg (hw i) (sq_nonneg ‖f i‖))
    (fun i _ => show (w i*‖f i‖)^2 ≤ w i*(w i*‖f i‖^2) by nlinarith)
  rw [hm,one_mul] at hs
  exact ((sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _))).mpr hn).trans hs

theorem idealAverageSet_energy_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (S : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealAverageSet P S f) ≤ idealLabelEnergy P M f := by
  have hj (a : MarkedPhysicalMarking P M) : ‖idealAverageSet P S f a‖^2 ≤
      ∑ b,idealLabelMass P M b*‖f (idealMix S a b)‖^2 :=
    idealWeightedJensen _ (idealLabelMass_nonneg P M hV) (idealLabelMass_sum P M hV) _
  calc
    _ ≤ ∑ a,idealLabelMass P M a*∑ b,idealLabelMass P M b*‖f (idealMix S a b)‖^2 :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hj a) (idealLabelMass_nonneg P M hV a)
    _ = _ := idealLabelExpectation_mix (A:=ℝ) P M hV S (fun a => ‖f a‖^2)

def IdealSymmetric {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (f : MarkedPhysicalMarking P M → ℂ) : Prop :=
  ∀ (π : J → Equiv.Perm (Fin M)) a,f (giantTwoSidedPermuteLabels π a)=f a

def idealProbeProjection {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (probes tail : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) : MarkedPhysicalMarking P M → ℂ :=
  fun a => ∑ T∈probes.powerset,(-1:ℂ)^T.card*idealAverageSet P (tail ∪ T) f a

end
end ArtinMatthews
