module

public import ArtinMatthews.GiantTwoSidedSharedDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Normalized harmonic restoration keeps the exact guarded dirty
damping. The error is the actual bad shared-list mass times the true
one-mark damping and the explicit overlap loss. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedSharedNormalizedDamping {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (k : ℕ) (q : ℝ) (w : ℕ) (b b' : (j : J) → ↥(P j)) : ℝ :=
  ∑ c : MarkedPhysicalMarking P k,
    markedPhysicalPadHarmonicMass P k c*giantTwoSidedSharedGuardedDamping q w b b' c

theorem giantTwoSidedSharedNormalizedDamping_error {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hV : ∀ j,0 < bandReciprocalMass (P j))
    (k w : ℕ) (b b' : (j : J) → ↥(P j))
    (hb : ∀ j,(b j:ℕ) ∣ w) (hb' : ∀ j,(b' j:ℕ) ∣ w+1)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ‖giantTwoSidedSharedNormalizedDamping k q w b b' -
      giantTwoSidedOneMarkDampingProduct P q w‖ ≤
      ((q⁻¹)^(2*(k*Fintype.card J))+1)*giantTwoSidedSharedBadMass P k w*
        giantTwoSidedOneMarkDampingProduct P q w := by
  let μ := markedPhysicalPadHarmonicMass P k
  let F (c : MarkedPhysicalMarking P k) := giantTwoSidedSharedGuardedDamping q w b b' c
  let B := giantTwoSidedOneMarkDampingProduct P q w
  let R := (q⁻¹)^(2*(k*Fintype.card J))
  have hB : 0 ≤ B := by unfold B giantTwoSidedOneMarkDampingProduct; positivity
  have hμ (c : MarkedPhysicalMarking P k) : 0 ≤ μ c := markedPhysicalPadHarmonicMass_nonneg P k hV c
  have hmass : (∑ c : MarkedPhysicalMarking P k,μ c*B)=B := by
    rw [← sum_mul,markedPhysicalPadHarmonicMass_sum P k hV,one_mul]
  have hdiff : (∑ c : MarkedPhysicalMarking P k,μ c*F c)-B =
      ∑ c : MarkedPhysicalMarking P k,μ c*(F c-B) := by
    simp only [mul_sub,sum_sub_distrib,hmass]
  change ‖(∑ c : MarkedPhysicalMarking P k,μ c*F c)-B‖ ≤
    (R+1)*giantTwoSidedSharedBadMass P k w*B
  rw [hdiff]
  calc
    _ ≤ ∑ c : MarkedPhysicalMarking P k,‖μ c*(F c-B)‖ := norm_sum_le _ _
    _ ≤ ∑ c : MarkedPhysicalMarking P k,
      ((R+1)*B)*((if ¬GiantTwoSidedSharedGood c w then (1:ℝ) else 0)*μ c) := by
        apply sum_le_sum
        intro c _
        by_cases hg : GiantTwoSidedSharedGood c w
        · have hF : F c = B := giantTwoSidedSharedGuardedDamping_eq_of_good hP hdis c b b' hb hb' hq.le hg
          simp only [hF,sub_self,mul_zero,norm_zero,ite_eq_right (not_not.mpr hg),zero_mul,le_refl]
        · have hF0 : 0 ≤ F c := giantTwoSidedSharedGuardedDamping_nonneg q b b' c
          have hF : F c ≤ R*B := giantTwoSidedSharedGuardedDamping_le hP hdis c b b' hb hb' hq hq1
          have hbound : ‖F c-B‖ ≤ (R+1)*B := by
            apply (norm_sub_le _ _).trans
            rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hF0,abs_of_nonneg hB,add_mul,one_mul]
            exact add_le_add hF le_rfl
          rw [ite_eq_left hg,one_mul,norm_mul,Real.norm_eq_abs (μ c),abs_of_nonneg (hμ c),mul_comm (μ c)]
          exact mul_le_mul_of_nonneg_right hbound (hμ c)
    _ = ((R+1)*B)*giantTwoSidedSharedBadMass P k w := by
      rw [← Finset.mul_sum]
      unfold giantTwoSidedSharedBadMass markedEventMass
      apply congrArg (fun z : ℝ => ((R+1)*B)*z)
      apply sum_congr rfl
      intro c _
      by_cases hg : GiantTwoSidedSharedGood c w <;> simp [hg,μ]
    _ = _ := by ring

end
end ArtinMatthews
