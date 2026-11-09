module

public import ArtinMatthews.GiantSignedRawEdgeSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The literal dirty multiplier is split into source promotion and remaining store terms. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}

def giantSignedRawPromoteMultiplier (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  if r.choice.2.1 = (fun _ => ∅) then 0 else 1

def giantSignedRawStoreOnlyMultiplier (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  if r.choice.2.1 = (fun _ => ∅) then
    if r.choice.1 = (fun _ => ∅) then 0 else 1
  else 0

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawDirtyMultiplier_split (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    giantSignedRawEdgeDirtyMultiplier s r =
      giantSignedRawPromoteMultiplier s r + giantSignedRawStoreOnlyMultiplier s r := by
  by_cases hT : r.choice.2.1 = (fun _ => ∅) <;>
    by_cases hS : r.choice.1 = (fun _ => ∅) <;>
    simp [giantSignedRawEdgeDirtyMultiplier, GiantSignedRawEdgeClean,
      giantSignedRawPromoteMultiplier, giantSignedRawStoreOnlyMultiplier, hT, hS]

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawPromoteMultiplier_norm (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawPromoteMultiplier s r‖ ≤ 1 := by
  unfold giantSignedRawPromoteMultiplier
  split_ifs <;> simp

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawStoreOnlyMultiplier_norm (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawStoreOnlyMultiplier s r‖ ≤ 1 := by
  unfold giantSignedRawStoreOnlyMultiplier
  split_ifs <;> simp

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedRawDirtyApply_split
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K
        (fun s r => η s r * giantSignedRawEdgeDirtyMultiplier s r) f s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K
        (fun s r => η s r * giantSignedRawPromoteMultiplier s r) f s +
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K
        (fun s r => η s r * giantSignedRawStoreOnlyMultiplier s r) f s := by
  unfold giantSignedRawEdgeApply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  dsimp only
  rw [giantSignedRawDirtyMultiplier_split]
  ring

end
end ArtinMatthews
