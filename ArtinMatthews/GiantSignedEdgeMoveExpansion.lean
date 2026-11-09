module

public import ArtinMatthews.GiantSignedEdgeStorePromote


set_option backward.privateInPublic true
@[expose] public section

/-! Individual actual edge choices in the source row. Reindexing retains
the old-index injection, fresh target mass and both pending factors. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    {t : B → ℕ}

def giantSignedEdgeMoveCoefficient (ν : (g : B) → P g → ℂ) (V : B → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source target : GiantSignedPrimeTuple P t)
    (m : GiantSignedMemory P) (c : GiantSignedEdgeChoice t m.1) : ℂ :=
  giantSignedPromotionCharge V (fun g => (c.2.1 g).card) *
    giantSignedFreshPrimeMass ν c.2.1 target *
      if GiantSignedEdgeHits d m target c ∧ GiantSignedEdgePromotionBan D c.2.1 target then
        (giantSignedPendingDamping ρ m : ℂ) *
          (giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source c) : ℂ)
      else 0

theorem giantSignedEdgeApply_eq_choice_sum (ν : (g : B) → P g → ℂ) (V : B → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ) (m : GiantSignedMemory P) :
    giantSignedEdgeApply ν V ρ d D source f m =
      ∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
        giantSignedEdgeMoveCoefficient ν V ρ d D source target m c *
          f target (giantSignedEdgeTarget d m source c) := by
  unfold giantSignedEdgeApply GiantSignedEdgeChoice
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : GiantSignedEdgeHits d m target ⟨S,T,e⟩ ∧
      GiantSignedEdgePromotionBan D T target
  · simp [giantSignedEdgeMoveCoefficient, h]
    ring
  · simp [giantSignedEdgeMoveCoefficient, h]

end
end ArtinMatthews
