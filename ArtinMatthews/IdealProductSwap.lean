module

public import ArtinMatthews.IdealProductAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Simultaneously swapping chosen coordinates preserves the two full
harmonic product laws exactly. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelExpectation_swap {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {M : ℕ}
    (S : Finset (G × Fin M))
    (F : MarkedPhysicalMarking P M → MarkedPhysicalMarking P M → A) :
    idealLabelExpectation P M (fun a => idealLabelExpectation P M
      (fun b => F (idealMix S a b) (idealMix S b a)))=
      idealLabelExpectation P M (fun a => idealLabelExpectation P M (F a)) := by
  have he := (idealMixEquiv (P:=P) S).sum_comp
    (fun z : MarkedPhysicalMarking P M × MarkedPhysicalMarking P M =>
      algebraMap ℝ A (idealLabelMass P M z.1*idealLabelMass P M z.2)*F z.1 z.2)
  simp only [idealMixEquiv,Equiv.coe_fn_mk,idealLabelMass_mix] at he
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at he
  unfold idealLabelExpectation
  simp only [mul_sum,← mul_assoc,← map_mul]
  exact he

theorem idealMix_eq_self_of_eq_outside {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S : Finset (G × Fin M)) (a b : MarkedPhysicalMarking P M)
    (h : ∀ g i,(g,i)∉S → b g i=a g i) : idealMix S a b=b := by
  funext g i
  simp only [idealMix]
  split_ifs with hi
  · rfl
  · exact (h g i hi).symm

end
end ArtinMatthews
