module

public import ArtinMatthews.MarkedPhysicalCofactorCoordinates
public import ArtinMatthews.MarkedPhysicalDetectorHarmonicSum


set_option backward.privateInPublic true
@[expose] public section

/-! Move the actual state-validity flags into the finite position fibers
at a fixed copied pad array and fixed last labels. No zero test, state
multiplicity or detector support is discarded. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalPosition_conditional_sum {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset (ℤ × ℤ)} (a : MarkedPhysicalMarking P M)
    (F : MarkedPhysicalPositions Z a → ℂ) :
    (∑ z : Z,if hz : MarkedPhysicalStateCondition z.1 a then F ⟨z,hz⟩ else 0)=
      ∑ z : MarkedPhysicalPositions Z a,F z := by
  exact Finset.sum_congr_set {z : Z | MarkedPhysicalStateCondition z.1 a}
    (fun z => if hz : MarkedPhysicalStateCondition z.1 a then F ⟨z,hz⟩ else 0) F
    (fun z hz => by
      change MarkedPhysicalStateCondition z.1 a at hz
      rw [dite_eq_left hz])
    (fun z hz => by
      change ¬MarkedPhysicalStateCondition z.1 a at hz
      rw [dite_eq_right hz])

theorem markedPhysicalPosition_double_conditional_sum {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset (ℤ × ℤ)} (a b : MarkedPhysicalMarking P M)
    (F : MarkedPhysicalPositions Z a → MarkedPhysicalPositions Z b → ℂ) :
    (∑ z : Z,∑ w : Z,if hz : MarkedPhysicalStateCondition z.1 a then
      if hw : MarkedPhysicalStateCondition w.1 b then F ⟨z,hz⟩ ⟨w,hw⟩ else 0 else 0)=
      ∑ z : MarkedPhysicalPositions Z a,∑ w : MarkedPhysicalPositions Z b,F z w := by
  have he (z : Z) : (∑ w : Z,if hz : MarkedPhysicalStateCondition z.1 a then
        if hw : MarkedPhysicalStateCondition w.1 b then F ⟨z,hz⟩ ⟨w,hw⟩ else 0 else 0)=
      if hz : MarkedPhysicalStateCondition z.1 a then
        ∑ w : MarkedPhysicalPositions Z b,F ⟨z,hz⟩ w else 0 := by
    by_cases hz : MarkedPhysicalStateCondition z.1 a
    · simp only [dite_eq_left hz]
      exact markedPhysicalPosition_conditional_sum b (F ⟨z,hz⟩)
    · simp only [dite_eq_right hz,Finset.sum_const_zero]
  simp_rw [he]
  exact markedPhysicalPosition_conditional_sum a (fun z => ∑ w : MarkedPhysicalPositions Z b,F z w)

variable {J : Type*} [Fintype J]
  (P : J → Finset ℕ) (pads : ℕ) (Z : Finset (ℤ × ℤ))
  (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
  (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))

def markedPhysicalPadValidPositionTerm
    (z : MarkedPhysicalPositions Z ((markedPhysicalMarkingSplit pads).symm (c,b)))
    (w : MarkedPhysicalPositions Z ((markedPhysicalMarkingSplit pads).symm (c,a))) : ℂ :=
  let D := markedPhysicalMarkingProduct c
  let bp : ℕ := ∏ j,(b j:ℕ)
  let ap : ℕ := ∏ j,(a j:ℕ)
  if (D:ℤ) ∣ markedMinorIntegerDet z.1.1 w.1.1 then
    if MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit pads).symm (c,b)) a then 0 else
      η ((bp:ℝ)/Y)*η ((ap:ℝ)/Y)*detector bp ap (markedMinorIntegerDet z.1.1 w.1.1/(D:ℤ))*
        star (markedPhysicalEndpointVector P (pads+1) α β z.1.1)*
        markedPhysicalEndpointVector P (pads+1) α β w.1.1
  else 0

theorem markedPhysicalPadDetectorResidual_positions :
    (∑ z : Z,∑ w : Z,markedPhysicalPadDetectorResidual P pads Z η Y detector
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) c b a z w)=
      ∑ z : MarkedPhysicalPositions Z ((markedPhysicalMarkingSplit pads).symm (c,b)),
        ∑ w : MarkedPhysicalPositions Z ((markedPhysicalMarkingSplit pads).symm (c,a)),
          markedPhysicalPadValidPositionTerm P pads Z η Y detector α β c b a z w := by
  simpa only [markedPhysicalPadDetectorResidual,markedPhysicalPadValidPositionTerm,Nat.cast_prod] using
    markedPhysicalPosition_double_conditional_sum _ _
      (markedPhysicalPadValidPositionTerm P pads Z η Y detector α β c b a)

end
end ArtinMatthews
