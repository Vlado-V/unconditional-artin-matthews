module

public import ArtinMatthews.GiantSignedRawEdgeMajorant
public import ArtinMatthews.GiantSignedRawPositiveSection
public import ArtinMatthews.GiantSignedRawAveraging


set_option backward.privateInPublic true
@[expose] public section

/-! Positive domination of the original raw edge preserves its exact
outer probability law and its actual store/promote kernel. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawPositiveCoefficient (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℝ :=
  giantSignedRawOuterWeight
    ((r.sourceSmallPermutation, r.sourceBigPermutation),
      (r.targetSmallPermutation, r.targetBigPermutation), r.auxiliary) *
    if IdealCopied C (giantSignedRawEdgeBigSource s r) r.bigTarget then
      giantSignedSmallEdgeWeight κ
        (giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
          giantTwoSidedPatternAuxiliaryProduct r.auxiliary) q
        (giantSignedRawEdgeSmallSource s r) r.smallTarget *
      ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
        (κ * (giantSignedRawEdgeProduct s r : ℤ)) (giantSignedRawEdgeProduct s r)
        (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
        (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice‖
    else 0

def giantSignedRawPositiveApply (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℝ)
    (s : GiantSignedState PS PB (k+ell)) : ℝ :=
  ∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
    giantSignedRawPositiveCoefficient ν V κ q ρ s r * f (giantSignedRawEdgeTarget κ s r)

omit [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val] in
theorem giantSignedRawPositiveCoefficient_nonneg
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ : ℝ)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    0 ≤ giantSignedRawPositiveCoefficient ν V κ q ρ s r := by
  unfold giantSignedRawPositiveCoefficient
  apply mul_nonneg (giantSignedRawOuterWeight_nonneg hVB _)
  split_ifs
  · exact mul_nonneg (giantSignedSmallEdgeWeight_nonneg _ _ _ _ _) (norm_nonneg _)
  · exact le_rfl

omit [∀ g, ∀ p : PB g, NeZero p.val] in
theorem giantSignedRawEdgeApply_norm_le_positive
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (ρ θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s‖ ≤
      W * giantSignedRawPositiveApply (C := C) ν V κ q ρ (fun t => ‖f t‖) s := by
  apply (giantSignedRawEdgeApply_norm_le ν V κ q ρ θ ζ K η hη f s).trans
  rw [giantSignedRawPositiveApply, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hc := giantSignedRawEdgeCoefficient_norm_le hPS hPB hVS hVB
    ν V κ hq ρ θ ζ W hW K hK s r
  have he : (if IdealCopied C (giantSignedRawEdgeBigSource s r) r.bigTarget then
      giantTwoSidedResidueSlotNormalization (J := S) (k+ell) *
        giantTwoSidedResidueSlotNormalization (J := B) (k+ell) *
        giantTwoSidedPatternAuxiliaryMass r.auxiliary * W *
        giantSignedSmallEdgeWeight κ
          (giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
            giantTwoSidedPatternAuxiliaryProduct r.auxiliary) q
          (giantSignedRawEdgeSmallSource s r) r.smallTarget *
        ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
          (κ * (giantSignedRawEdgeProduct s r : ℤ)) (giantSignedRawEdgeProduct s r)
          (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
          (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice‖ else 0) =
        W * giantSignedRawPositiveCoefficient ν V κ q ρ s r := by
    unfold giantSignedRawPositiveCoefficient giantSignedRawOuterWeight
    split_ifs <;> ring
  rw [he] at hc
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f (giantSignedRawEdgeTarget κ s r)))

theorem giantSignedRawPositiveApply_average
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (f : GiantSignedState PS PB (k+ell) → ℝ) (hf : ∀ s, 0 ≤ f s)
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawPositiveApply (C := C) ν V κ q ρ f s =
      ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i *
        ‖giantSignedRawCoreApply ν V κ q ρ i.2.2
          (fun t => (f ((giantTwoSidedResiduePermute i.2.1.1).symm t.1,
            (giantSignedGroupedTuplePermutation i.2.1.2).symm t.2.1, t.2.2) : ℂ))
          (giantSignedStatePermute PS i.1.1 i.1.2 s)‖ := by
  unfold giantSignedRawPositiveApply
  rw [← (giantSignedRawEdgeMoveEquiv (PS := PS) (C := C) s.2.2).symm.sum_comp
    (fun r => giantSignedRawPositiveCoefficient ν V κ q ρ s r * f (giantSignedRawEdgeTarget κ s r))]
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
    ‖giantSignedRawCoreApply ν V κ q ρ aux
      (fun t => (f ((giantTwoSidedResiduePermute τS).symm t.1,
        (giantSignedGroupedTuplePermutation τB).symm t.2.1, t.2.2) : ℂ))
      (giantTwoSidedResiduePermute πS s.1,
        giantSignedGroupedTuplePermutation πB s.2.1, s.2.2)‖
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

end
end ArtinMatthews
