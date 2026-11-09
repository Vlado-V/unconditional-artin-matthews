module

public import ArtinMatthews.GiantSignedRawPositiveAverage
public import ArtinMatthews.GiantSignedRawSourceGateMass


set_option backward.privateInPublic true
@[expose] public section

/-! The original positive row retains a gate on each actual outer section. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawPositiveGate_average
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (gate : GiantSignedRawOuterChoice (S := S) PB C ell → Prop)
    (f : GiantSignedState PS PB (k+ell) → ℝ) (hf : ∀ s, 0 ≤ f s)
    (s : GiantSignedState PS PB (k+ell)) :
    (∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
      giantSignedRawPositiveCoefficient ν V κ q ρ s r *
        (if gate (giantSignedRawMoveOuter r) then f (giantSignedRawEdgeTarget κ s r) else 0)) =
      ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i *
        (if gate i then
          ‖giantSignedRawCoreApply ν V κ q ρ i.2.2
            (fun t => (f ((giantTwoSidedResiduePermute i.2.1.1).symm t.1,
              (giantSignedGroupedTuplePermutation i.2.1.2).symm t.2.1, t.2.2) : ℂ))
            (giantSignedStatePermute PS i.1.1 i.1.2 s)‖
        else 0) := by
  rw [← (giantSignedRawEdgeMoveEquiv (PS := PS) (C := C) s.2.2).symm.sum_comp
    (fun r => giantSignedRawPositiveCoefficient ν V κ q ρ s r *
      (if gate (giantSignedRawMoveOuter r) then f (giantSignedRawEdgeTarget κ s r) else 0))]
  simp only [GiantSignedRawOuterChoice, GiantSignedStateSlotPermutations,
    Fintype.sum_prod_type, giantSignedRawEdgeMoveEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
  apply Finset.sum_congr rfl
  intro πS _
  apply Finset.sum_congr rfl
  intro πB _
  apply Finset.sum_congr rfl
  intro τS _
  apply Finset.sum_congr rfl
  intro τB _
  apply Finset.sum_congr rfl
  intro aux _
  change _ = (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) *
    giantTwoSidedResidueSlotNormalization (J := B) (k+ell) * giantTwoSidedPatternAuxiliaryMass aux) *
    (if gate ((πS,πB),(τS,τB),aux) then
      ‖giantSignedRawCoreApply ν V κ q ρ aux
        (fun t => (f ((giantTwoSidedResiduePermute τS).symm t.1,
          (giantSignedGroupedTuplePermutation τB).symm t.2.1, t.2.2) : ℂ))
        (giantTwoSidedResiduePermute πS s.1,
          giantSignedGroupedTuplePermutation πB s.2.1, s.2.2)‖
    else 0)
  by_cases hg : gate ((πS,πB),(τS,τB),aux)
  · simp only [giantSignedRawMoveOuter, hg, ite_true]
    rw [← giantSignedRawPositiveSection_eq_core_norm ν hν V hV κ q hρ aux τS τB f hf
      (giantTwoSidedResiduePermute πS s.1) (giantSignedGroupedTuplePermutation πB s.2.1) s.2.2]
    simp only [giantSignedRawPositiveCoefficient, giantSignedRawOuterWeight,
      giantSignedRawEdgeSmallSource, giantSignedRawEdgeBigSource,
      giantSignedRawEdgeProduct, giantSignedRawEdgeTarget,
      giantSignedRawPositiveSection, giantSignedSmallPrefixProduct]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs with h
    · simp only [h, ite_true]
      ring
    · simp only [h, ite_false, mul_zero, zero_mul]
  · simp [giantSignedRawMoveOuter, hg]

end
end ArtinMatthews
