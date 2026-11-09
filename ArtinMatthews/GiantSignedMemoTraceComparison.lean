module

public import ArtinMatthews.GiantSignedTraceMemo
public import ArtinMatthews.GiantSignedTraceProjection


set_option backward.privateInPublic true
@[expose] public section

/-! A finite signed event is dominated by its genuine accepted
absolute trace mass on the full dependent trace. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v w
variable {X : Type u} {M : Type w}

theorem giantSignedMemoTraceComparison (f : X → ℂ) (rs : List (GiantSignedTraceRow.{u,v} X))
    (c : GiantSignedTraceMemoRules M rs) (m : M) (x : X)
    (good : GiantSignedTrace rs x → Prop) (hfinite : Finite {t : GiantSignedTrace rs x // good t})
    (event : {t : GiantSignedTrace rs x // good t} → Prop)
    (haccept : ∀ t, event t → GiantSignedTraceMemoAccept rs c m x t.val) :
    ENNReal.ofReal ‖∑' t : {t : GiantSignedTrace rs x // good t},
      giantSignedTraceWeight f rs x t.val * (if event t then 1 else 0)‖ ≤
      giantSignedTraceMemoMass f rs c m x := by
  let G : Set (GiantSignedTrace rs x) := {t | good t}
  let _ : Fintype G := @Fintype.ofFinite _ hfinite
  let F (t : G) := giantSignedTraceWeight f rs x t.val * (if event t then 1 else 0)
  let W (t : GiantSignedTrace rs x) : ℝ≥0∞ :=
    if h : t ∈ G then ENNReal.ofReal ‖F ⟨t,h⟩‖ else 0
  have hW (t : G) : W t.val = ENNReal.ofReal ‖F t‖ := dite_eq_left t.property
  calc
    _ ≤ ENNReal.ofReal (∑ t : G, ‖F t‖) := by
      apply ENNReal.ofReal_le_ofReal
      change ‖∑' t : G, F t‖ ≤ _
      rw [tsum_fintype]
      exact norm_sum_le _ _
    _ = ∑ t : G, ENNReal.ofReal ‖F t‖ := ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)
    _ = ∑' t : G, W t.val := by
      rw [tsum_fintype]
      exact Finset.sum_congr rfl (fun t _ => (hW t).symm)
    _ = ∑' t, G.indicator W t := tsum_subtype G W
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro t
      by_cases ht : t ∈ G
      · rw [Set.indicator_of_mem ht]
        change W t ≤ if GiantSignedTraceMemoAccept rs c m x t then _ else 0
        have hw : W t = ENNReal.ofReal ‖F ⟨t,ht⟩‖ := dite_eq_left ht
        rw [hw]
        by_cases he : event ⟨t,ht⟩
        · rw [ite_eq_left (haccept ⟨t,ht⟩ he)]
          simp only [F, ite_eq_left he, mul_one, le_refl]
        · simp only [F, ite_eq_right he, mul_zero, norm_zero, ENNReal.ofReal_zero, zero_le]
      · rw [Set.indicator_of_notMem ht]
        exact zero_le

end
end ArtinMatthews
