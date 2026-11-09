module

public import ArtinMatthews.GiantSignedRawGateAverage
public import ArtinMatthews.GiantSignedRawRareSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The projected original promotion row is dominated by its actual gated core sections. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawCoreAbsoluteSection (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (s : GiantSignedState PS PB (k+ell)) : ℝ :=
  ‖giantSignedRawCoreApply ν V κ q ρ i.2.2
    (fun t => (‖f ((giantSignedStatePermute PS i.2.1.1 i.2.1.2).symm t)‖ : ℂ))
    (giantSignedStatePermute PS i.1.1 i.1.2 s)‖

theorem giantSignedRawEdgeCoefficient_norm_le_positiveCoefficient
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (ρ θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ ≤
      W * giantSignedRawPositiveCoefficient ν V κ q ρ s r := by
  refine (giantSignedRawEdgeCoefficient_norm_le hPS hPB hVS hVB ν V κ hq ρ θ ζ W hW K hK s r).trans_eq ?_
  unfold giantSignedRawPositiveCoefficient giantSignedRawOuterWeight
  split_ifs <;> ring

theorem giantSignedRawProjectedPromote_norm_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) {q ρ : ℝ} (hq : 0 ≤ q) (hρ : 0 ≤ ρ)
    (θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (N : ℕ) (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedStateMemoryCutoff N
      (giantSignedRawEdgeApply ν V κ q ρ θ ζ K
        (fun s r => η s r * giantSignedRawPromoteMultiplier s r)
        (giantSignedStateMemoryCutoff N f)) s‖ ≤
      W * ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i *
        (if GiantSignedRawOuterCappedSourceGate N κ s i then
          giantSignedRawCoreAbsoluteSection ν V κ q ρ (giantSignedStateMemoryCutoff N f) i s
        else 0) := by
  let fN := giantSignedStateMemoryCutoff N f
  by_cases hs : (∑ g, s.2.2.1 g) ≤ N
  · rw [giantSignedStateMemoryCutoff_of_le N _ s hs]
    have hgate := giantSignedRawPositiveGate_average (C := C) ν hν V hV κ q hρ
      (GiantSignedRawOuterCappedSourceGate N κ s) (fun t => ‖fN t‖) (fun _ => norm_nonneg _) s
    change _ = (∑ i : GiantSignedRawOuterChoice (S := S) PB C ell,
      giantSignedRawOuterWeight i * (if GiantSignedRawOuterCappedSourceGate N κ s i then
        giantSignedRawCoreAbsoluteSection ν V κ q ρ fN i s else 0)) at hgate
    change _ ≤ W * ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell,
      giantSignedRawOuterWeight i * (if GiantSignedRawOuterCappedSourceGate N κ s i then
        giantSignedRawCoreAbsoluteSection ν V κ q ρ fN i s else 0)
    rw [← hgate, Finset.mul_sum]
    unfold giantSignedRawEdgeApply
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r _
    dsimp only
    by_cases hg : GiantSignedRawOuterCappedSourceGate N κ s (giantSignedRawMoveOuter r)
    · rw [ite_eq_left hg, ← mul_assoc W (giantSignedRawPositiveCoefficient ν V κ q ρ s r),
        norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hmult : ‖η s r * giantSignedRawPromoteMultiplier s r‖ ≤ 1 := by
        rw [norm_mul]
        calc
          _ ≤ 1 * ‖giantSignedRawPromoteMultiplier s r‖ :=
            mul_le_mul_of_nonneg_right (hη s r) (norm_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using giantSignedRawPromoteMultiplier_norm s r
      calc
        _ ≤ ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ * 1 :=
          mul_le_mul_of_nonneg_left hmult (norm_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          exact giantSignedRawEdgeCoefficient_norm_le_positiveCoefficient hPS hPB hVS hVB
            ν V κ hq ρ θ ζ W hW K hK s r
    · rw [ite_eq_right hg, mul_zero, mul_zero]
      by_cases hc : giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r = 0
      · simp [hc]
      by_cases hT : r.choice.2.1 = (fun _ => ∅)
      · simp [giantSignedRawPromoteMultiplier, hT]
      have hsource := giantSignedRawEdgeCoefficient_promotion_sourceRareGate
        ν V κ q ρ θ ζ K s r hc hT
      exact False.elim (hg ⟨hs, (giantSignedRawSourceRareGate_outer κ s r).mp hsource⟩)
  · rw [giantSignedStateMemoryCutoff_of_lt N _ s (lt_of_not_ge hs)]
    simp [GiantSignedRawOuterCappedSourceGate, hs]

end
end ArtinMatthews
