module

public import ArtinMatthews.GiantSignedTraceEdgeAbsolute
public import ArtinMatthews.GiantSignedRawEdgeSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the actual edge phase commutes with relabelling the old
pending indices. -/
namespace ArtinMatthews
noncomputable section
universe u

theorem giantSignedRawEdgeAbsoluteMultiplier_old_permute
    {S B : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell)) (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 σ))
    (hη : η (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
      η s (giantSignedRawEdgeOldEquiv s.2.2 σ r)) :
    giantSignedRawEdgeAbsoluteMultiplier ν V κ q ρ θ ζ K η
        (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
      giantSignedRawEdgeAbsoluteMultiplier ν V κ q ρ θ ζ K η s
        (giantSignedRawEdgeOldEquiv s.2.2 σ r) := by
  unfold giantSignedRawEdgeAbsoluteMultiplier
  rw [giantSignedRawEdgeCoefficient_old_permute ν V κ q ρ θ ζ K s σ r, hη]

end
end ArtinMatthews
