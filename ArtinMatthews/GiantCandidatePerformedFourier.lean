module

public import ArtinMatthews.GiantTwoSidedGroupReindexTransport
public import ArtinMatthews.GiantSignedJoinedSourceFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The exact selected group carrier of the root replacement theorem
has the same signed Fourier moment as its split small/big carrier. -/
namespace ArtinMatthews
noncomputable section

theorem giantCandidatePerformedFourier_eq_split {I : Type*} {x : ℝ}
    (groups : Finset (GiantCandidateGroupIndex x))
    [∀ p : ↥(markedPhysicalBandPrimes (fun j : ↥groups => giantCandidateGroup x j.val)), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim (giantCandidatePerformedSmallBand groups)
      (giantCandidatePerformedBigBand groups))), NeZero p.val]
    (hdis : Pairwise (fun i j : ↥groups => Disjoint (giantCandidateGroup x i.val) (giantCandidateGroup x j.val)))
    {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → GiantCandidatePerformedBig groups → Finset (Fin k)) (κ : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) (C i p) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedExpandedIndependentFourierMoment patterns (fun i p => giantCandidatePerformedPattern groups (C i p))
      κ q ζ (fun i p => giantCandidatePerformedCoefficient groups (K i p)) θ =
      giantTwoSidedExpandedIndependentFourierMoment patterns
        (fun i p => giantSignedJoinedPattern (S := GiantCandidatePerformedSmall groups) (C i p)) κ q ζ
        (fun i p => giantSignedJoinedCoefficient (PS := giantCandidatePerformedSmallBand groups) (K i p)) θ := by
  symm
  refine giantTwoSidedExpandedIndependentFourierMoment_reindex (giantCandidatePerformedSplitEquiv groups)
    (giantCandidatePerformedSplit_band groups) hdis patterns _ _
    (fun i p => giantCandidatePerformedSplit_pattern groups (C i p)) κ q ζ _ _ ?_ θ
  intro i p a b z
  rfl

end
end ArtinMatthews
