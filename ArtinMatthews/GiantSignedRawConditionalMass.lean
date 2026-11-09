module

public import ArtinMatthews.GiantSignedRawConditionalSector


set_option backward.privateInPublic true
@[expose] public section

/-! Reassemble the conditional fresh-label estimates over the exact raw
moves and their original auxiliary and endpoint averages. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawEdgeConditionalMass
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (s : GiantSignedState PS PB (k+ell))
    (Gate : (c : GiantSignedEdgeChoice (fun g => ell+(C g).card) s.2.2.1) →
      GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card) → Prop)
    (w : GiantSignedMemory PB → ℝ) : ℝ :=
  ∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
    if Gate r.choice (giantSignedRawEdgeFreshLabels r) then
      ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ *
        w (giantSignedRawEdgeTarget κ s r).2.2 else 0

omit [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
private theorem rawCoefficient_norm_le_positive
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (ρ θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ ≤
      W * giantSignedRawPositiveCoefficient ν V κ q ρ s r := by
  refine (giantSignedRawEdgeCoefficient_norm_le hPS hPB hVS hVB ν V κ hq ρ θ ζ W hW K hK s r).trans_eq ?_
  unfold giantSignedRawPositiveCoefficient giantSignedRawOuterWeight
  split_ifs <;> ring

theorem giantSignedRawEdgeConditionalMass_le_positive
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν μ : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (hμ : ∀ g p, 0 ≤ μ g p)
    (V : B → ℝ) (κ : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (ρ θ ζ W F : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell))
    (Gate : (c : GiantSignedEdgeChoice (fun g => ell+(C g).card) s.2.2.1) →
      GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card) → Prop)
    (hGate : ∀ c, (∑ fresh : GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card),
        if Gate c fresh then ∏ g, ∏ i, ν g (fresh g i) else 0) ≤
      F * ∏ g, (∑ p : PB g, μ g p)^((c.2.1 g)ᶜ).card)
    (w : GiantSignedMemory PB → ℝ) (hw : ∀ m, 0 ≤ w m) :
    giantSignedRawEdgeConditionalMass ν V κ q ρ θ ζ K s Gate w ≤
      W * F * giantSignedRawPositiveApply (C := C) μ V κ q ρ (fun t => w t.2.2) s := by
  let R := GiantSignedRawEdgeMove PS PB ell C s.2.2
  let f (r : R) : ℝ := if Gate r.choice (giantSignedRawEdgeFreshLabels r) then
    giantSignedRawPositiveCoefficient ν V κ q ρ s r * w (giantSignedRawEdgeTarget κ s r).2.2 else 0
  let g (r : R) : ℝ := giantSignedRawPositiveCoefficient μ V κ q ρ s r *
    w (giantSignedRawEdgeTarget κ s r).2.2
  have hsum : (∑ r : R, f r) ≤ F * ∑ r : R, g r := by
    let e := giantSignedRawEdgeMoveEquiv (PS := PS) (ell := ell) (C := C) s.2.2
    rw [← e.symm.sum_comp f, ← e.symm.sum_comp g]
    simp only [Fintype.sum_prod_type, e, giantSignedRawEdgeMoveEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro πS _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro πB _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro τS _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro τB _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro aux _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    exact giantSignedRawPositiveTargetConditional_le (PS := PS) (ell := ell) (C := C) hVB ν μ hν hμ V κ q ρ s
      πS τS πB τB aux c z (Gate c) F (hGate c) w hw
  calc
    _ ≤ W * ∑ r : R, f r := by
      unfold giantSignedRawEdgeConditionalMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      dsimp only [f]
      by_cases h : Gate r.choice (giantSignedRawEdgeFreshLabels r)
      · rw [if_pos h, if_pos h, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (rawCoefficient_norm_le_positive hPS hPB hVS hVB ν V κ hq ρ θ ζ W hW K hK s r) (hw _)
      · rw [if_neg h, if_neg h, mul_zero]
    _ ≤ W * (F * ∑ r : R, g r) := mul_le_mul_of_nonneg_left hsum hW
    _ = _ := (mul_assoc W F _).symm

end
end ArtinMatthews
