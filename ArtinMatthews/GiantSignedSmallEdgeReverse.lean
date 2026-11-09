module

public import ArtinMatthews.GiantSignedSmallEdgeKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact pointwise reversal of the actual small residue weight. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Type*} [Fintype S] {PS : S → Finset ℕ} {k ell : ℕ}

private theorem small_pattern_abs_reverse
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    {C : S → Finset (Fin k)} (d : ℤ) {q : ℝ} (hq : 0 ≤ q) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PS C ell)
    (s t : GiantTwoSidedResidueState PS (k+ell)) (aux : GiantTwoSidedPatternAuxiliary PS C) :
    ‖giantTwoSidedResiduePatternCoefficient d q ζ K s t aux‖ =
      ‖giantTwoSidedResiduePatternCoefficient (-d) q ζ (fun a b c => K b a c) t s aux‖ := by
  have h : GiantTwoSidedResiduePatternCondition C d s t aux ↔
      GiantTwoSidedResiduePatternCondition C (-d) t s aux := by
    constructor
    · exact giantTwoSidedResiduePatternCondition_reverse C d s t aux
    · intro h
      simpa only [neg_neg] using giantTwoSidedResiduePatternCondition_reverse C (-d) t s aux h
  rw [giantTwoSidedResiduePatternCoefficient_norm hPS hVS _ hq,
    giantTwoSidedResiduePatternCoefficient_norm hPS hVS _ hq, ← h]
  split_ifs
  · ring
  · rfl

theorem giantSignedSmallEdgeWeight_reverse
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (κ : ℤ) (D : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (s t : GiantTwoSidedResidueState PS (k+ell)) :
    giantSignedSmallEdgeWeight κ D q s t = giantSignedSmallEdgeWeight (-κ) D q t s := by
  unfold giantSignedSmallEdgeWeight
  rw [neg_mul]
  exact small_pattern_abs_reverse hPS hVS (κ * (D : ℤ)) hq 0 _ s t _

end
end ArtinMatthews
