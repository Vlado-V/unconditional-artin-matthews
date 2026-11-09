module

public import ArtinMatthews.MarkedPhysicalPadValidPositions


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fixed-pad kernel on natural cofactor coordinates. Its
determinant is b*m*n-a*r*s, and the original four endpoint coefficients
are recovered with their literal roughness and cross-ban tests. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem markedPhysicalPad_append_product {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)
    (c : MarkedPhysicalMarking P pads) (b : (j : J) → ↥(P j)) :
    markedPhysicalMarkingProduct ((markedPhysicalMarkingSplit pads).symm (c,b))=
      markedPhysicalMarkingProduct c * ∏ j,(b j:ℕ) := by
  have h := markedPhysicalMarkingProduct_split P hP pads (markedPhysicalPadRawSource P hP pads c b)
  rw [markedPhysicalPadRawSource_copied,markedPhysicalPadRawSource_last] at h
  simpa only [markedPhysicalPadRawSource,Equiv.apply_symm_apply] using h

def markedPhysicalPadCofactorTerm {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (pads : ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
    (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j)) (v u : ℕ × ℕ) : ℂ :=
  let bp : ℕ := ∏ j,(b j:ℕ)
  let ap : ℕ := ∏ j,(a j:ℕ)
  if MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit pads).symm (c,b)) a then 0 else
    if MarkedPhysicalBandRough P v.1 ∧ MarkedPhysicalBandRough P u.1 then
      η ((bp:ℝ)/Y)*η ((ap:ℝ)/Y)*
        detector bp ap ((bp:ℤ)*v.1*u.2-(ap:ℤ)*u.1*v.2)*
        (α v.1*conj (α u.1)*β u.2*conj (β v.2)) else 0

theorem markedPhysicalPadValidPositionTerm_cofactor
    {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,0≤z.1 ∧ 0≤z.2)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
    (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))
    (v : MarkedPhysicalCofactorCoordinates (Z := Z) ((markedPhysicalMarkingSplit pads).symm (c,b)))
    (u : MarkedPhysicalCofactorCoordinates (Z := Z) ((markedPhysicalMarkingSplit pads).symm (c,a))) :
    markedPhysicalPadValidPositionTerm P pads Z η Y detector α β c b a
      ((markedPhysicalPositionCofactorEquiv hP hdis hZ ((markedPhysicalMarkingSplit pads).symm (c,b))).symm v)
      ((markedPhysicalPositionCofactorEquiv hP hdis hZ ((markedPhysicalMarkingSplit pads).symm (c,a))).symm u)=
      markedPhysicalPadCofactorTerm P pads η Y detector α β c b a v.1 u.1 := by
  let B := (markedPhysicalMarkingSplit pads).symm (c,b)
  let A := (markedPhysicalMarkingSplit pads).symm (c,a)
  let z := (markedPhysicalPositionCofactorEquiv hP hdis hZ B).symm v
  let w := (markedPhysicalPositionCofactorEquiv hP hdis hZ A).symm u
  let D := markedPhysicalMarkingProduct c
  let bp : ℕ := ∏ j,(b j:ℕ)
  let ap : ℕ := ∏ j,(a j:ℕ)
  have hz : z.1.1=markedPhysicalLift (D*bp) v.1.1 v.1.2 := by
    change markedPhysicalLift (markedPhysicalMarkingProduct B) _ _=_
    exact congrArg (fun l => markedPhysicalLift l v.1.1 v.1.2)
      (markedPhysicalPad_append_product P hP pads c b)
  have hw : w.1.1=markedPhysicalLift (D*ap) u.1.1 u.1.2 := by
    change markedPhysicalLift (markedPhysicalMarkingProduct A) _ _=_
    exact congrArg (fun l => markedPhysicalLift l u.1.1 u.1.2)
      (markedPhysicalPad_append_product P hP pads c a)
  have hdvd : (D:ℤ) ∣ markedMinorIntegerDet z.1.1 w.1.1 := by
    rw [hz,hw,markedPhysicalLift_det]
    exact dvd_mul_right _ _
  have hdet : markedMinorIntegerDet z.1.1 w.1.1/(D:ℤ)=
      (bp:ℤ)*v.1.1*u.1.2-(ap:ℤ)*u.1.1*v.1.2 := by
    rw [hz,hw]
    exact markedPhysicalLift_det_quotient (markedPhysicalMarkingProduct_pos hP c) bp ap _ _ _ _
  have hB : markedPhysicalEndpointVector P (pads+1) α β z.1.1=
      if MarkedPhysicalBandRough P v.1.1 then conj (α v.1.1)*β v.1.2 else 0 :=
    markedPhysicalCofactorCoordinates_endpoint hP hdis B α β v
  have hA : markedPhysicalEndpointVector P (pads+1) α β w.1.1=
      if MarkedPhysicalBandRough P u.1.1 then conj (α u.1.1)*β u.1.2 else 0 :=
    markedPhysicalCofactorCoordinates_endpoint hP hdis A α β u
  change markedPhysicalPadValidPositionTerm P pads Z η Y detector α β c b a z w=_
  unfold markedPhysicalPadValidPositionTerm markedPhysicalPadCofactorTerm
  dsimp only
  rw [ite_eq_left hdvd,hdet,hB,hA]
  by_cases hb : MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit pads).symm (c,b)) a
  · rw [ite_eq_left hb,ite_eq_left hb]
  · rw [ite_eq_right hb,ite_eq_right hb]
    by_cases hv : MarkedPhysicalBandRough P v.1.1 <;> by_cases hu : MarkedPhysicalBandRough P u.1.1 <;>
      simp [hv,hu,bp,ap]
    ring

end
end ArtinMatthews
