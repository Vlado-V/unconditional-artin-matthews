module

public import ArtinMatthews.IdealSymmetricCoefficients
public import ArtinMatthews.IdealProductSymmetry
public import Mathlib.Logic.Equiv.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! The symmetric coefficient bound tensorizes across arbitrary group
blocks without imposing a product form on the test vector. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSingleGroupPermutation {J : Type*} [DecidableEq J] {P : J → Finset ℕ} {M : ℕ}
    (g : J) (π : Equiv.Perm (Fin M)) (t : MarkedPhysicalMarking P M) : MarkedPhysicalMarking P M :=
  giantTwoSidedPermuteLabels (Function.update (fun _ => Equiv.refl (Fin M)) g π) t

theorem idealSingleGroupPermutation_same {J : Type*} [DecidableEq J] {P : J → Finset ℕ} {M : ℕ}
    (g : J) (π : Equiv.Perm (Fin M)) (t : MarkedPhysicalMarking P M) :
    idealSingleGroupPermutation g π t g=idealCoefficientPermutation π (t g) := by
  funext i
  simp [idealSingleGroupPermutation,giantTwoSidedPermuteLabels,idealCoefficientPermutation]

theorem idealSingleGroupPermutation_other {J : Type*} [DecidableEq J] {P : J → Finset ℕ} {M : ℕ}
    (g : J) (π : Equiv.Perm (Fin M)) (t : MarkedPhysicalMarking P M) {j : J} (hj : j≠g) :
    idealSingleGroupPermutation g π t j=t j := by
  funext i
  simp [idealSingleGroupPermutation,giantTwoSidedPermuteLabels,Function.update_of_ne hj]

theorem idealCoefficientGroup_bound {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (g : J) (a₀ : ↥(P g))
    (c : MarkedPhysicalMarking P M → ℂ)
    (hc : ∀ π t,c (idealSingleGroupPermutation g π t)=c t)
    (probes tail : Finset (Fin M)) (hPT : Disjoint probes tail) (hM : 0 < M)
    (hm : 1 ≤ probes.card) (hell : 1 ≤ tail.card)
    (hlarge : (probes.card+tail.card)*(probes.card+tail.card-1) ≤ M) :
    (∑ t,if probes ⊆ idealCoefficientSupport a₀ (t g) ∧
        Disjoint (idealCoefficientSupport a₀ (t g)) tail then ‖c t‖^2 else 0) ≤
      (2/(probes.card+1 : ℕ))*∑ t,‖c t‖^2 := by
  let e := Equiv.piSplitAt g (fun j => Fin M → ↥(P j))
  have hrow (r : ∀ j : {j : J // j≠g},Fin M → ↥(P j))
      (π : Equiv.Perm (Fin M)) (v : Fin M → ↥(P g)) :
      c (e.symm (idealCoefficientPermutation π v,r))=c (e.symm (v,r)) := by
    have he : e.symm (idealCoefficientPermutation π v,r)=
        idealSingleGroupPermutation g π (e.symm (v,r)) := by
      funext j i
      by_cases hj : j=g
      · subst j
        simp [e,Equiv.piSplitAt,idealSingleGroupPermutation,giantTwoSidedPermuteLabels,
          idealCoefficientPermutation]
      · simp [e,Equiv.piSplitAt,idealSingleGroupPermutation,giantTwoSidedPermuteLabels,
          hj]
    rw [he,hc]
  have hsum (F : MarkedPhysicalMarking P M → ℝ) :
      (∑ t,F t)=∑ r,∑ v,F (e.symm (v,r)) := by
    rw [← e.symm.sum_comp,Fintype.sum_prod_type,sum_comm]
  rw [hsum,hsum,mul_sum]
  apply sum_le_sum
  intro r _
  simpa only [e,Equiv.piSplitAt,Equiv.coe_fn_symm_mk,dite_true,eq_rec_constant] using
    idealCoefficientSupportEnergy_probe_bound a₀ (fun v => c (e.symm (v,r)))
      (hrow r) probes tail hPT hM hm hell hlarge

def IdealCoefficientBlockEvent {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a₀ : ∀ j,↥(P j)) (probes tail : J → Finset (Fin M)) (G : Finset J)
    (t : MarkedPhysicalMarking P M) : Prop :=
  ∀ j∈G,probes j ⊆ idealCoefficientSupport (a₀ j) (t j) ∧
    Disjoint (idealCoefficientSupport (a₀ j) (t j)) (tail j)

theorem idealCoefficientBlockEvent_other {J : Type*} [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (a₀ : ∀ j,↥(P j)) (probes tail : J → Finset (Fin M))
    (G : Finset J) (g : J) (hg : g∉G) (π : Equiv.Perm (Fin M))
    (t : MarkedPhysicalMarking P M) :
    IdealCoefficientBlockEvent a₀ probes tail G (idealSingleGroupPermutation g π t) ↔
      IdealCoefficientBlockEvent a₀ probes tail G t := by
  have he (j : J) (hj : j∈G) : idealSingleGroupPermutation g π t j=t j :=
    idealSingleGroupPermutation_other g π t (fun h => hg (h ▸ hj))
  simp only [IdealCoefficientBlockEvent]
  constructor <;> intro h j hj <;> simpa only [he j hj] using h j hj

theorem idealCoefficientTensor_bound {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (a₀ : ∀ j,↥(P j))
    (c : MarkedPhysicalMarking P M → ℂ) (hc : IdealSymmetric c)
    (probes tail : J → Finset (Fin M)) (G : Finset J)
    (hPT : ∀ j∈G,Disjoint (probes j) (tail j)) (hM : 0 < M)
    (hm : ∀ j∈G,1 ≤ (probes j).card) (hell : ∀ j∈G,1 ≤ (tail j).card)
    (hlarge : ∀ j∈G,((probes j).card+(tail j).card)*((probes j).card+(tail j).card-1) ≤ M) :
    (∑ t,if IdealCoefficientBlockEvent a₀ probes tail G t then ‖c t‖^2 else 0) ≤
      (∏ j∈G,((2:ℝ)/((probes j).card+1 : ℕ)))*∑ t,‖c t‖^2 := by
  induction G using Finset.induction_on with
  | empty => simp [IdealCoefficientBlockEvent]
  | @insert g G hg ih =>
    let d (t : MarkedPhysicalMarking P M) :=
      if IdealCoefficientBlockEvent a₀ probes tail G t then c t else 0
    have hd (π : Equiv.Perm (Fin M)) (t : MarkedPhysicalMarking P M) :
        d (idealSingleGroupPermutation g π t)=d t := by
      simp only [d,idealCoefficientBlockEvent_other a₀ probes tail G g hg]
      rw [show c (idealSingleGroupPermutation g π t)=c t from hc _ t]
    have hstep := idealCoefficientGroup_bound g (a₀ g) d hd (probes g) (tail g)
      (hPT g (mem_insert_self g G)) hM (hm g (mem_insert_self g G))
      (hell g (mem_insert_self g G)) (hlarge g (mem_insert_self g G))
    have hleft :
        (∑ t,if IdealCoefficientBlockEvent a₀ probes tail (insert g G) t then ‖c t‖^2 else 0)=
        ∑ t,if probes g ⊆ idealCoefficientSupport (a₀ g) (t g) ∧
          Disjoint (idealCoefficientSupport (a₀ g) (t g)) (tail g) then ‖d t‖^2 else 0 := by
      apply sum_congr rfl
      intro t _
      have hi : IdealCoefficientBlockEvent a₀ probes tail (insert g G) t ↔
          (probes g ⊆ idealCoefficientSupport (a₀ g) (t g) ∧
            Disjoint (idealCoefficientSupport (a₀ g) (t g)) (tail g)) ∧
            IdealCoefficientBlockEvent a₀ probes tail G t := by
        simp only [IdealCoefficientBlockEvent,mem_insert,forall_eq_or_imp]
      rw [hi]
      by_cases hp : probes g ⊆ idealCoefficientSupport (a₀ g) (t g) ∧
          Disjoint (idealCoefficientSupport (a₀ g) (t g)) (tail g)
      · by_cases ht : IdealCoefficientBlockEvent a₀ probes tail G t
        · simp only [hp,ht,true_and,ite_true,d]
        · simp only [hp,ht,true_and,ite_true,ite_false,d,norm_zero]
          norm_num
      · simp only [hp,false_and,ite_false]
    have hnorm : (∑ t,‖d t‖^2)=
        ∑ t,if IdealCoefficientBlockEvent a₀ probes tail G t then ‖c t‖^2 else 0 := by
      apply sum_congr rfl
      intro t _
      simp only [d]
      split_ifs <;> simp
    rw [hleft]
    apply hstep.trans
    rw [hnorm,prod_insert hg]
    exact (mul_le_mul_of_nonneg_left
      (ih (fun j hj => hPT j (mem_insert_of_mem hj))
        (fun j hj => hm j (mem_insert_of_mem hj))
        (fun j hj => hell j (mem_insert_of_mem hj))
        (fun j hj => hlarge j (mem_insert_of_mem hj))) (by positivity)).trans_eq (mul_assoc _ _ _).symm

end
end ArtinMatthews
