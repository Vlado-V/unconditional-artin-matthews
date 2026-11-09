module

public import ArtinMatthews.GiantComparisonGuardedDamping


set_option backward.privateInPublic true
@[expose] public section

/-! After the copied labels are averaged, the damping differs from the
independent endpoint weights by the actual copied bad mass and the
unshared auxiliary exclusion. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {C : J → Finset (Fin k)}

def giantComparisonRestoredSharedDamping (aux : GiantTwoSidedPatternAuxiliary P C)
    (q : ℝ) (w w' : ℕ) (b b' : GiantComparisonFreeLabels P C ell) : ℝ :=
  ∑ c : GiantComparisonSharedLabels P C,
    giantComparisonSharedMass c * giantComparisonGuardedDamping aux q w w' b b' c

theorem giantComparisonRestoredSharedDamping_eq_zero_of_aux_hit
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ)
    (b b' : GiantComparisonFreeLabels P C ell) (haux : ¬ GiantComparisonUnsharedAuxAvoids aux b b') :
    giantComparisonRestoredSharedDamping aux q w w' b b' = 0 := by
  unfold giantComparisonRestoredSharedDamping
  apply sum_eq_zero
  intro c _
  have hn : ¬ GiantComparisonSharedAdmissible aux c b b' := fun hc => haux hc.auxAvoids
  simp only [giantComparisonGuardedDamping, ite_eq_right hn, mul_zero]

theorem giantComparisonRestoredSharedDamping_error
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (aux : GiantTwoSidedPatternAuxiliary P C) {w w' : ℕ}
    (b : GiantComparisonFreeMarking P C ell w) (b' : GiantComparisonFreeMarking P C ell w')
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ‖giantComparisonRestoredSharedDamping aux q w w' b.val b'.val -
      giantComparisonIndependentDamping P C ell q w w'‖ ≤
      (((q⁻¹)^(2*(k*Fintype.card J))+1)*giantComparisonSharedBadMass aux w w' +
        (if GiantComparisonUnsharedAuxAvoids aux b.val b'.val then 0 else 1))*
      giantComparisonIndependentDamping P C ell q w w' := by
  let B := giantComparisonIndependentDamping P C ell q w w'
  let R := (q⁻¹)^(2*(k*Fintype.card J))
  let μ (c : GiantComparisonSharedLabels P C) := giantComparisonSharedMass c
  let F (c : GiantComparisonSharedLabels P C) := giantComparisonGuardedDamping aux q w w' b.val b'.val c
  have hB : 0 ≤ B := by unfold B giantComparisonIndependentDamping giantComparisonQuotientDamping; positivity
  have hR : 0 ≤ R := by unfold R; positivity
  have hμ (c : GiantComparisonSharedLabels P C) : 0 ≤ μ c :=
    giantTwoSidedPatternAuxiliaryMass_nonneg hV c
  by_cases haux : GiantComparisonUnsharedAuxAvoids aux b.val b'.val
  · rw [ite_eq_left haux, add_zero]
    have hm : (∑ c : GiantComparisonSharedLabels P C, μ c*B) = B := by
      rw [← sum_mul]
      change (∑ c : GiantComparisonSharedLabels P C, giantComparisonSharedMass c)*B = B
      rw [giantComparisonSharedMass_sum C hV, one_mul]
    have hd : (∑ c : GiantComparisonSharedLabels P C, μ c*F c)-B =
        ∑ c : GiantComparisonSharedLabels P C, μ c*(F c-B) := by
      simp only [mul_sub,sum_sub_distrib,hm]
    change ‖(∑ c : GiantComparisonSharedLabels P C, μ c*F c)-B‖ ≤
      (R+1)*giantComparisonSharedBadMass aux w w'*B
    rw [hd]
    calc
      _ ≤ ∑ c : GiantComparisonSharedLabels P C, ‖μ c*(F c-B)‖ := norm_sum_le _ _
      _ ≤ ∑ c : GiantComparisonSharedLabels P C,
          ((R+1)*B)*(if GiantComparisonSharedGood aux w w' c then 0 else μ c) := by
        apply sum_le_sum
        intro c _
        by_cases hg : GiantComparisonSharedGood aux w w' c
        · have hf : F c = B := giantComparisonGuardedDamping_eq_of_good hP hdis aux b b' haux hg hq.le
          simp only [ite_eq_left hg, hf, sub_self, mul_zero, norm_zero, le_refl]
        · rw [ite_eq_right hg,norm_mul,Real.norm_eq_abs (μ c),abs_of_nonneg (hμ c),mul_comm (μ c)]
          apply mul_le_mul_of_nonneg_right _ (hμ c)
          have hf0 : 0 ≤ F c := giantComparisonGuardedDamping_nonneg aux q w w' b.val b'.val c
          have hf : F c ≤ R*B := giantComparisonGuardedDamping_le hP hdis aux c b b' hq hq1
          refine (norm_sub_le _ _).trans ?_
          rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hf0,abs_of_nonneg hB,add_mul,one_mul]
          exact add_le_add hf le_rfl
      _ = _ := by
        rw [← mul_sum]
        change (R+1)*B*giantComparisonSharedBadMass aux w w' =
          (R+1)*giantComparisonSharedBadMass aux w w'*B
        ring
  · rw [giantComparisonRestoredSharedDamping_eq_zero_of_aux_hit aux q w w' b.val b'.val haux,
      ite_eq_right haux,zero_sub,norm_neg]
    change ‖B‖ ≤ ((R+1)*giantComparisonSharedBadMass aux w w'+1)*B
    rw [Real.norm_eq_abs,abs_of_nonneg hB]
    have hbad : 0 ≤ giantComparisonSharedBadMass aux w w' := by
      unfold giantComparisonSharedBadMass
      apply sum_nonneg
      intro c _
      split_ifs
      · exact le_rfl
      · exact hμ c
    have hunit : 1 ≤ (R+1)*giantComparisonSharedBadMass aux w w'+1 := by
      exact le_add_of_nonneg_left (mul_nonneg (by positivity) hbad)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hunit hB

end
end ArtinMatthews
