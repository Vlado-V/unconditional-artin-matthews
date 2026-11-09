module

public import ArtinMatthews.GiantSignedEdgeConditionalSector
public import ArtinMatthews.GiantSignedRawPositiveAverage


set_option backward.privateInPublic true
@[expose] public section

/-! For a fixed actual retrieval and store choice, changing the fresh
target law acts on its ordered unpromoted coordinates alone. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}

def giantSignedRawEdgeFreshLabels {m : GiantSignedMemory PB}
    (r : GiantSignedRawEdgeMove PS PB ell C m) :
    GiantSignedPrimeTuple PB (fun g => ((r.choice.2.1 g)ᶜ).card) :=
  (giantSignedEdgeTargetLabelEquiv r.choice.2.1 (giantSignedPatternFreeLabels C r.bigTarget)).2

theorem giantSignedRawPositiveTargetConditional_le
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν μ : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (hμ : ∀ g p, 0 ≤ μ g p)
    (V : B → ℝ) (κ : ℤ) (q ρ : ℝ)
    (s : GiantSignedState PS PB (k+ell))
    (πS τS : S → Equiv.Perm (Fin (k+ell))) (πB τB : B → Equiv.Perm (Fin (k+ell)))
    (aux : GiantTwoSidedPatternAuxiliary PB C)
    (c : GiantSignedEdgeChoice (fun g => ell + (C g).card) s.2.2.1)
    (z : GiantTwoSidedResidueState PS (k+ell))
    (Gate : GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card) → Prop)
    (F : ℝ)
    (hGate : (∑ fresh : GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card),
        if Gate fresh then ∏ g, ∏ i, ν g (fresh g i) else 0) ≤
      F * ∏ g, (∑ p : PB g, μ g p)^((c.2.1 g)ᶜ).card)
    (w : GiantSignedMemory PB → ℝ) (hw : ∀ m, 0 ≤ w m) :
    let r (b : MarkedPhysicalMarking PB (k+ell)) : GiantSignedRawEdgeMove PS PB ell C s.2.2 :=
      ⟨πS,πB,τS,τB,aux,c,z,b⟩
    (∑ b : MarkedPhysicalMarking PB (k+ell),
      if Gate (giantSignedRawEdgeFreshLabels (r b)) then
        giantSignedRawPositiveCoefficient ν V κ q ρ s (r b) *
          w (giantSignedRawEdgeTarget κ s (r b)).2.2 else 0) ≤
    F * ∑ b : MarkedPhysicalMarking PB (k+ell),
      giantSignedRawPositiveCoefficient μ V κ q ρ s (r b) *
        w (giantSignedRawEdgeTarget κ s (r b)).2.2 := by
  dsimp only
  let A := MarkedPhysicalMarking PB (k+ell)
  let T := GiantSignedPrimeTuple PB (fun g => ell + (C g).card)
  let Fresh := GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card)
  let a := giantSignedGroupedTuplePermutation πB s.2.1
  let y := giantTwoSidedResiduePermute πS s.1
  let D₀ := giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux
  let D := giantSignedSmallPrefixProduct y * D₀
  let E := giantSignedEdgeTargetLabelEquiv (P := PB) c.2.1
  let r (b : A) : GiantSignedRawEdgeMove PS PB ell C s.2.2 := ⟨πS,πB,τS,τB,aux,c,z,b⟩
  let U := giantSignedRawOuterWeight ((πS,πB),(τS,τB),aux)
  let J := giantSignedSmallEdgeWeight κ D₀ q y z
  let out := giantSignedEdgeTarget (κ * (D : ℤ)) s.2.2 (giantSignedPatternFreeLabels C a) c
  let H := U * J * w out
  let Z (law : ∀ g, PB g → ℝ) (t : T) :=
    ‖giantSignedEdgeMoveCoefficient (fun g p => (law g p : ℂ)) V ρ
      (κ * (D : ℤ)) D (giantSignedPatternFreeLabels C a) t s.2.2 c‖
  have hH : 0 ≤ H := mul_nonneg
    (mul_nonneg (giantSignedRawOuterWeight_nonneg hVB _) (giantSignedSmallEdgeWeight_nonneg _ _ _ _ _))
    (hw out)
  have hsum (law : ∀ g, PB g → ℝ) (G : Fresh → Prop) :
      (∑ b : A, if G (giantSignedRawEdgeFreshLabels (r b)) then
        giantSignedRawPositiveCoefficient law V κ q ρ s (r b) *
          w (giantSignedRawEdgeTarget κ s (r b)).2.2 else 0) =
      H * ∑ t : T, if G (E t).2 then Z law t else 0 := by
    calc
      _ = ∑ b : A, if IdealCopied C a b then
            H * (if G (E (giantSignedPatternFreeLabels C b)).2 then
              Z law (giantSignedPatternFreeLabels C b) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        let t := giantSignedPatternFreeLabels C b
        change (if G (E t).2 then
            U * (if IdealCopied C a b then J * Z law t else 0) * w out else 0) =
          (if IdealCopied C a b then H * (if G (E t).2 then Z law t else 0) else 0)
        by_cases hc : IdealCopied C a b <;> by_cases hg : G (E t).2 <;>
          simp only [hc, hg, ite_true, ite_false, H, mul_zero, zero_mul]
        ring
      _ = ∑ t : T, H * (if G (E t).2 then Z law t else 0) := by
        rw [← giantSignedCopiedTarget_plain_sum C a]
        simp only [giantSignedPatternFreeLabels_fill]
        apply Finset.sum_congr rfl
        intro t _
        by_cases hg : G (E t).2 <;> simp only [hg, ite_true, ite_false]
      _ = _ := (Finset.mul_sum ..).symm
  have hμsum := hsum μ (fun _ => True)
  simp only [ite_true] at hμsum
  change (∑ b : A, if Gate (giantSignedRawEdgeFreshLabels (r b)) then
        giantSignedRawPositiveCoefficient ν V κ q ρ s (r b) *
          w (giantSignedRawEdgeTarget κ s (r b)).2.2 else 0) ≤
      F * ∑ b : A, giantSignedRawPositiveCoefficient μ V κ q ρ s (r b) *
        w (giantSignedRawEdgeTarget κ s (r b)).2.2
  rw [hsum ν Gate, hμsum]
  have he : (∑ t : T, if Gate (E t).2 then Z ν t else 0) ≤ F * ∑ t : T, Z μ t :=
    giantSignedEdgeConditionalSector_le ν μ hν hμ V ρ (κ * (D : ℤ)) D
      (giantSignedPatternFreeLabels C a) s.2.2 c Gate F hGate
  exact (mul_le_mul_of_nonneg_left he hH).trans_eq (mul_left_comm H F _)

end
end ArtinMatthews
