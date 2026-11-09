module

public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeCharged


set_option backward.privateInPublic true
@[expose] public section

/-! Exact degree normal form of the original charged edge action.  The
literal admissible choice payload supplies the subset, hit and target-slot
indicators used by the proved coupled factorial component. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem markedRawEdge_charged_memory_choice_sum
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) *
      markedRawEdgeChargedApply ν δ γ hZ K (fun _ => 1) (x,(active,m))) =
      ∑ y : Z, ∑ a : MarkedRawEdgeDegreeShape J B,
        ∑ data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a,
          markedRawEdgeDegreeChoicePairing ν δ γ hZ x active y a data K := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  unfold markedRawEdgeChargedApply
  simp only [mul_one, Finset.mul_sum]
  have h := markedRawEdge_memory_degree_sum (B := B) hZ x active
    (fun c => (markedRawMemoryMass ν c.1 : ℂ) *
      (markedRawEdgeChoiceCharge δ γ hZ (x,(active,c.1)) c.2 *
        markedRawEdgeChoiceFreshMass ν hZ (x,(active,c.1)) c.2 *
        K (x,(active,c.1)) (markedRawEdgeTargetState hZ (x,(active,c.1)) c.2)))
  dsimp only at h
  rw [h]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro data _
  unfold markedRawEdgeDegreeChoicePairing
  ring

/-- Full actual memory integration at one source position and copied
prefix, with every active last label and both total cutoffs retained. -/
theorem markedRawEdge_charged_memory_normalForm
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (copied : MarkedRawActive P pads)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ last : (j : J) → ↥(P j), (markedRawLastMass ν last : ℂ) *
      ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) *
        markedRawEdgeChargedApply ν δ γ hZ K (fun _ => 1)
          (x,((markedRawActiveSplit pads).symm (copied,last),m))) =
      ∑ y : Z, ∑ t : MarkedRawEdgeDegrees J B,
        markedRawEdgeDegreePairing P (fun j p => (ν j p : ℂ)) hZ x y copied t δ γ K := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  calc
    _ = ∑ y : Z, ∑ t : MarkedRawEdgeDegrees J B,
        ∑ last : (j : J) → ↥(P j), (markedRawLastMass ν last : ℂ) *
          ∑ S : (j : J) → MarkedRawDeletionBatch
            (t.survivors j + markedRawEdgeBit (t.promoted j)) (markedRawEdgeBit (t.promoted j)),
            ∑ data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) ⟨t,S⟩,
              markedRawEdgeDegreeChoicePairing ν δ γ hZ x
                ((markedRawActiveSplit pads).symm (copied,last)) y ⟨t,S⟩ data K := by
      simp_rw [markedRawEdge_charged_memory_choice_sum]
      simp only [Fintype.sum_sigma, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro t _
      unfold markedRawEdgeDegreePairing
      apply Finset.sum_congr rfl
      intro last _
      rw [markedRawEdge_degree_component_sum]
      simp only [markedRawLastMass, Complex.ofReal_prod]

end
end ArtinMatthews
