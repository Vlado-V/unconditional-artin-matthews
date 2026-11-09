module

public import ArtinMatthews.GiantSignedRawCleanChoice
public import ArtinMatthews.GiantSignedRawEdgeSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The selected clean row is the clean part of the original raw row's
proved partition, with the same coefficient and target map. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    {C : B → Finset (Fin k)}

omit [Fintype B] [DecidableEq B] [DecidableEq S]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawEdgeClean_iff_choiceClean {m : GiantSignedMemory PB}
    (r : GiantSignedRawEdgeMove PS PB ell C m) :
    GiantSignedRawEdgeClean r ↔ GiantSignedEdgeChoiceClean r.choice := Iff.rfl

theorem giantSignedRawCleanApply_eq_split
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCleanApply ν V κ q ρ θ ζ K f s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K giantSignedRawEdgeCleanMultiplier f s := rfl

theorem giantSignedRawEdgeApply_one_eq_clean_add_dirty
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K (fun _ _ => 1) f s =
      giantSignedRawCleanApply ν V κ q ρ θ ζ K f s +
        giantSignedRawEdgeApply ν V κ q ρ θ ζ K giantSignedRawEdgeDirtyMultiplier f s := by
  simpa only [one_mul, giantSignedRawCleanApply_eq_split] using
    giantSignedRawEdgeApply_clean_add_dirty ν V κ q ρ θ ζ K (fun _ _ => 1) f s

end
end ArtinMatthews
