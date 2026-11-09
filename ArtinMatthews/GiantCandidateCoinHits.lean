module

public import ArtinMatthews.GiantCandidateCoinSuccess
public import ArtinMatthews.GiantCandidateHitSelections


set_option backward.privateInPublic true
@[expose] public section

/-! The actual coin test uses exactly the two hit counts whose binomial
moments are computed on rough product dyads. -/
namespace ArtinMatthews

theorem giantCandidateCoinSuccess_eq_hitCounts (x c q : ℝ) (j v : ℕ)
    (i : GiantCandidateGroupIndex x) :
    giantCandidateCoinSuccess x c q j v i =
      giantCandidateCoinTest c q j (bandReciprocalMass (giantCandidateGroup x i))
        (giantCandidateHitSet (giantCandidateGroup x i) .predecessor v).card
        (giantCandidateHitSet (giantCandidateGroup x i) .product v).card := by
  rfl

end ArtinMatthews
