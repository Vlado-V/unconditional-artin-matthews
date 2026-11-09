module

public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealProductAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Averaging is self-adjoint for the actual harmonic pairing. This
gives the exact zero contribution from an unused mean-zero probe. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelPairing_average_adjoint {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (S : Finset (J × Fin M))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P (idealAverageSet P S f) g=idealLabelPairing P f (idealAverageSet P S g) := by
  have hstar (r : ℝ) : star (r:ℂ)=(r:ℂ) := by
    exact Complex.conj_ofReal r
  have hmix (a b : MarkedPhysicalMarking P M) :
      idealMix S (idealMix S a b) (idealMix S b a)=a := by
    funext j i
    simp only [idealMix]
    split_ifs <;> rfl
  have he := (idealMixEquiv (P:=P) S).sum_comp
    (fun z : MarkedPhysicalMarking P M × MarkedPhysicalMarking P M =>
      ((idealLabelMass P M z.1*idealLabelMass P M z.2:ℝ):ℂ)*star (f z.1)*g (idealMix S z.1 z.2))
  simp only [idealMixEquiv,Equiv.coe_fn_mk,idealLabelMass_mix,hmix] at he
  calc
    _ = ∑ z : MarkedPhysicalMarking P M × MarkedPhysicalMarking P M,
        ((idealLabelMass P M z.1*idealLabelMass P M z.2:ℝ):ℂ)*
          star (f (idealMix S z.1 z.2))*g z.1 := by
      rw [Fintype.sum_prod_type]
      unfold idealLabelPairing idealAverageSet idealLabelExpectation
      simp only [star_sum,star_mul,RCLike.algebraMap_eq_ofReal,mul_sum,sum_mul,Complex.ofReal_mul]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      calc
        _ = (idealLabelMass P M a:ℂ)*
            (star (f (idealMix S a b))*(idealLabelMass P M b:ℂ))*g a :=
          congrArg (fun z : ℂ => (idealLabelMass P M a:ℂ)*(star (f (idealMix S a b))*z)*g a)
            (hstar (idealLabelMass P M b))
        _ = _ := by ac_rfl
    _ = ∑ z : MarkedPhysicalMarking P M × MarkedPhysicalMarking P M,
        ((idealLabelMass P M z.1*idealLabelMass P M z.2:ℝ):ℂ)*
          star (f z.1)*g (idealMix S z.1 z.2) := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold idealLabelPairing idealAverageSet idealLabelExpectation
      simp only [RCLike.algebraMap_eq_ofReal,mul_sum,Complex.ofReal_mul]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ac_rfl

theorem idealLabelPairing_meanZero {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (S : Finset (J × Fin M))
    (f g : MarkedPhysicalMarking P M → ℂ)
    (hf : idealAverageSet P S f=0) (hg : idealAverageSet P S g=g) :
    idealLabelPairing P f g=0 := by
  rw [← hg,← idealLabelPairing_average_adjoint,hf]
  simp [idealLabelPairing]

theorem idealAverageSet_mul_of_independent {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (S : Finset (J × Fin M))
    (phase f : MarkedPhysicalMarking P M → ℂ)
    (hphase : ∀ a b,phase (idealMix S a b)=phase a) :
    idealAverageSet P S (fun a => phase a*f a)=fun a => phase a*idealAverageSet P S f a := by
  funext a
  unfold idealAverageSet idealLabelExpectation
  simp only [hphase,mul_sum]
  apply sum_congr rfl
  intro b _
  ring

end
end ArtinMatthews
