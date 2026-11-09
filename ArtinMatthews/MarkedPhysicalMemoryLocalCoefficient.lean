module

public import ArtinMatthews.MarkedPhysicalCoordinateLabelCopies
public import ArtinMatthews.MarkedMemoryHistoryPrimeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The physical coordinate copy is the actual raw memory edge residual
times its original V factor. Its target copy permutation is the inverse
of the memory edge's final slot permutation. No kernel is divided out. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedPhysicalCoordinateKernel_joint
    (s t : MarkedRawState P (pads+1) B Z)
    (hs : MarkedRawActiveDistinct s.2.1) (ht : MarkedRawActiveDistinct t.2.1) :
    markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q s.2.1 t.2.1 s.1.1 t.1.1=
      ((∏ j,(V j)⁻¹:ℝ):ℂ)*
        (if ((markedRawActiveSplit pads) s.2.1).1=((markedRawActiveSplit pads) t.2.1).1 then
          markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) s t else 0) := by
  have he (l b a : ℤ) : l-b+a=0 ↔ l=b-a := by omega
  unfold markedPhysicalCoordinateKernel markedRawEdgeJointCoefficient
  simp only [markedRawEndpointFactor,hs,ht,ite_true,one_pow,Complex.ofReal_one,mul_one,
    markedBan_minor_integral,markedBanEdgeKernel,he,mul_assoc]

theorem markedPhysicalCoordinateKernel_rawChoice
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s)
    (hs : MarkedRawActiveDistinct s.2.1)
    (ht : MarkedRawActiveDistinct (markedRawEdgeTargetState hZ s c).2.1) :
    markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q s.2.1
        (markedRawEdgeTargetState hZ s c).2.1 s.1.1 c.target.1=
      ((∏ j,(V j)⁻¹:ℝ):ℂ)*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) s c := by
  change markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q s.2.1
    (markedRawEdgeTargetState hZ s c).2.1 s.1.1 (markedRawEdgeTargetState hZ s c).1.1=_
  rw [markedPhysicalCoordinateKernel_joint hZ V ψ η d₀ Y Q s _ hs ht,
    markedRawEdgeChoiceCoefficient_eq_joint]
  have hp : ((markedRawActiveSplit pads) s.2.1).1=
      ((markedRawActiveSplit pads) (markedRawEdgeTargetState hZ s c).2.1).1 := by
    change _=((markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm _)).1
    rw [Equiv.apply_symm_apply]
  rw [ite_eq_left hp]

omit [Fintype J] [DecidableEq J] in
theorem markedRawActiveDistinct_slot
    (a : MarkedRawActive P (pads+1)) (ha : MarkedRawActiveDistinct a)
    (σ : J → Equiv.Perm (Fin (pads+1))) :
    MarkedRawActiveDistinct (markedRawActiveSlotEquiv σ a) := by
  intro j
  exact (ha j).comp (σ j).injective

variable (PN : J → Finset ℕ) (hP : ∀ j p,p∈PN j → p.Prime)

theorem markedPhysicalCoordinateLabelCopy_memory
    (k : ℕ) (s : MarkedRawState (fun j => markedRawPrimeBand (PN j)) (pads+1) B Z)
    (edge : MarkedMemoryEdgeChoice hZ s)
    (hs : MarkedRawActiveDistinct s.2.1)
    (ht : MarkedRawActiveDistinct (markedMemoryEdgeChoiceTarget hZ s edge).2.1) :
    markedPhysicalCoordinateLabelCopy PN hP V pads ψ η d₀ Y Q k
      (markedPhysicalMarkingEquiv PN hP (pads+1) s.2.1)
      (markedPhysicalMarkingEquiv PN hP (pads+1) (markedMemoryEdgeChoiceTarget hZ s edge).2.1)
      (edge.1,fun j => (edge.2.2 j).symm) s.1.1 (markedMemoryEdgeChoiceTarget hZ s edge).1.1=
      ((∏ j,(V j)⁻¹:ℝ):ℂ)*
        (if k%2=0 then markedMemoryEdgeResidual hZ ψ η d₀ Y Q (fun _ => 1) s edge
          else markedMemoryEdgeResidual hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
            d₀ Y Q (fun _ => 1) s edge) := by
  have hsrc : (markedPhysicalMarkingEquiv PN hP (pads+1)).symm
      (fun j l => markedPhysicalMarkingEquiv PN hP (pads+1) s.2.1 j (edge.1 j l))=
      (markedRawSlotEquiv edge.1 s).2.1 := rfl
  have htgt : (markedPhysicalMarkingEquiv PN hP (pads+1)).symm
      (fun j l => markedPhysicalMarkingEquiv PN hP (pads+1)
        (markedMemoryEdgeChoiceTarget hZ s edge).2.1 j ((edge.2.2 j).symm l))=
      (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 s) edge.2.1).2.1 := by
    funext j l
    change (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 s) edge.2.1).2.1 j
      (edge.2.2 j ((edge.2.2 j).symm l))=_
    rw [Equiv.apply_symm_apply]
  have hsrcd := markedRawActiveDistinct_slot s.2.1 hs edge.1
  have htgtd : MarkedRawActiveDistinct
      (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 s) edge.2.1).2.1 := by
    intro j a b hab
    have hh := (ht j) (show (markedMemoryEdgeChoiceTarget hZ s edge).2.1 j ((edge.2.2 j).symm a)=
      (markedMemoryEdgeChoiceTarget hZ s edge).2.1 j ((edge.2.2 j).symm b) by
        change (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 s) edge.2.1).2.1 j
          (edge.2.2 j ((edge.2.2 j).symm a))=
          (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 s) edge.2.1).2.1 j
            (edge.2.2 j ((edge.2.2 j).symm b))
        simpa only [Equiv.apply_symm_apply] using hab)
    exact (edge.2.2 j).symm.injective hh
  unfold markedPhysicalCoordinateLabelCopy
  rw [hsrc,htgt]
  change ((Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)⁻¹)^2 *
    (if k%2=0 then markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q
      else markedPhysicalCoordinateKernel V pads (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u)) d₀ Y Q)
      (markedRawSlotEquiv edge.1 s).2.1
      (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 s) edge.2.1).2.1
      (markedRawSlotEquiv edge.1 s).1.1 edge.2.1.target.1 = _
  by_cases hk : k%2=0
  · rw [ite_eq_left hk,ite_eq_left hk,
      markedPhysicalCoordinateKernel_rawChoice hZ V ψ η d₀ Y Q _ edge.2.1 hsrcd htgtd]
    unfold markedMemoryEdgeResidual
    ring
  · rw [ite_eq_right hk,ite_eq_right hk,
      markedPhysicalCoordinateKernel_rawChoice hZ V (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q _ edge.2.1 hsrcd htgtd]
    unfold markedMemoryEdgeResidual
    ring

end
end ArtinMatthews
