module

public import ArtinMatthews.GiantSignedFixedOrderedLifespan
public import ArtinMatthews.GiantSignedJoinedBigLifespanSupport
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantTwoSidedExpandedFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The original scalar on a fixed guarded path and its supported big
lifespans, before the ordered birth multiplicities are introduced. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedFixedLifespanSourceWeight
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (θ : AddCircle (1 : ℝ)) (c : GiantSignedFixedLifespanChoices path (markedMemoryVisitQ q n)) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ)^n) *
    giantTwoSidedRootScalar (giantSignedChronologicalJoinedPattern C) path.labels
      path.sourcePermutation path.targetPermutation path.auxiliary ζ
      (fun i => giantSignedJoinedCoefficient (PS := PS) (K i)) *
    ((giantTwoSidedIndependentResidueFactor PS (giantSignedSmallMarking path.labels) q path.offset
      path.smallRoot / Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ) *
    fourier (path.offset (Fin.last n)) θ *
    (giantSignedJoinedBigLifespanNormalizedProduct path.labels path.offset (markedMemoryVisitQ q n) c.val : ℂ)

end
end ArtinMatthews
