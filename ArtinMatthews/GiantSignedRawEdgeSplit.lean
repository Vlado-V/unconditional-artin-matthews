module

public import ArtinMatthews.GiantSignedRawEdgeData


set_option backward.privateInPublic true
@[expose] public section

/-! Clean and dirty terms are selected from the same actual full row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    {C : B → Finset (Fin k)}

def GiantSignedRawEdgeClean {m : GiantSignedMemory PB}
    (r : GiantSignedRawEdgeMove PS PB ell C m) : Prop :=
  r.choice.1 = (fun _ => ∅) ∧ r.choice.2.1 = (fun _ => ∅)

def giantSignedRawEdgeCleanMultiplier (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  if GiantSignedRawEdgeClean r then 1 else 0

def giantSignedRawEdgeDirtyMultiplier (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  if GiantSignedRawEdgeClean r then 0 else 1

omit [Fintype B] [DecidableEq B] [DecidableEq S]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawEdgeCleanMultiplier_norm (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawEdgeCleanMultiplier s r‖ ≤ 1 := by
  unfold giantSignedRawEdgeCleanMultiplier
  split_ifs <;> simp

omit [Fintype B] [DecidableEq B] [DecidableEq S]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawEdgeDirtyMultiplier_norm (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawEdgeDirtyMultiplier s r‖ ≤ 1 := by
  unfold giantSignedRawEdgeDirtyMultiplier
  split_ifs <;> simp

theorem giantSignedRawEdgeApply_clean_add_dirty (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K
        (fun s r => η s r * giantSignedRawEdgeCleanMultiplier s r) f s +
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K
        (fun s r => η s r * giantSignedRawEdgeDirtyMultiplier s r) f s := by
  unfold giantSignedRawEdgeApply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : GiantSignedRawEdgeClean r <;>
    simp [giantSignedRawEdgeCleanMultiplier, giantSignedRawEdgeDirtyMultiplier, h]

end
end ArtinMatthews
