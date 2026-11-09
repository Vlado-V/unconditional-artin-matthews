module

public import ArtinMatthews.GiantSignedSmallFreeEdgeData
public import ArtinMatthews.GiantSignedPatternFiberEnergy
public import ArtinMatthews.GiantSignedRawEdgeData


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical full-state core and its exact copied-label fibers. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawCoreApply (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
  giantSignedSmallFreeEdgeApply ν V κ q ρ
    (giantTwoSidedPatternCopiedProduct C s.2.1 * giantTwoSidedPatternAuxiliaryProduct aux)
    (fun z a m => f (z, giantSignedPatternFill C s.2.1 a, m))
    s.1 (giantSignedPatternFreeLabels C s.2.1) s.2.2

theorem giantSignedRawCoreApply_sourceFill
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ : ℝ)
    (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (c : GiantSignedPatternCopiedLabels PB C)
    (s : GiantTwoSidedResidueState PS (k+ell))
    (a : GiantSignedPrimeTuple PB (fun g => ell + (C g).card)) (m : GiantSignedMemory PB) :
    giantSignedRawCoreApply ν V κ q ρ aux f (s, giantSignedPatternSourceFill C c a, m) =
      giantSignedSmallFreeEdgeApply ν V κ q ρ
        (giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct aux)
        (fun z b out => f (z, giantSignedPatternSourceFill C c b, out)) s a m := by
  simp only [giantSignedRawCoreApply, giantSignedPatternSourceFill_product,
    giantSignedPatternSourceFill_freeLabels, giantSignedPatternSourceFill_patternFill]


end
end ArtinMatthews
