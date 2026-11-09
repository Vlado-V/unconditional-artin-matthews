module

public import ArtinMatthews.GiantSignedGhostConditionalRow
public import ArtinMatthews.GiantSignedGhostBatchLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The finite sectors enumerate the original countable ghost moves
whose ordered batches fit the address frame. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] {P : B → Finset ℕ}

abbrev GiantSignedGhostFiniteBatches (m : GiantSignedMemory P) (H : ℕ) :=
  Σ _ : (∀ g, Finset (Fin (m.1 g))), Σ b : B → Fin (H+1), ∀ g, Fin (b g).val → P g

def giantSignedGhostFiniteBatchEquiv (m : GiantSignedMemory P) (H : ℕ) :
    GiantSignedGhostFiniteBatches m H ≃
      {r : GiantSignedGhostMemoryMoves m // GiantSignedGhostBatchFits H r} where
  toFun z := ⟨giantSignedGhostFiniteBatchMove m z.1 z.2.1 z.2.2, fun g =>
    Nat.le_of_lt_succ (z.2.1 g).isLt⟩
  invFun r := ⟨fun g => (r.val g).1,
    fun g => ⟨(r.val g).2.1,Nat.lt_succ_of_le (r.property g)⟩,
    fun g => (r.val g).2.2⟩
  left_inv z := by
    rcases z with ⟨d,b,p⟩
    rfl
  right_inv r := by
    apply Subtype.ext
    funext g
    change (⟨(r.val g).1,(r.val g).2.1,(r.val g).2.2⟩ :
      GiantSignedGhostMoves (giantSignedMemoryGroupEquiv P m g)) = r.val g
    rcases r.val g with ⟨d,b,p⟩
    rfl

theorem giantSignedGhostFiniteBatch_tsum {R : Type*} [AddCommMonoid R] [TopologicalSpace R] [T2Space R]
    (m : GiantSignedMemory P) (H : ℕ)
    (F : {r : GiantSignedGhostMemoryMoves m // GiantSignedGhostBatchFits H r} → R) :
    (∑' r : GiantSignedGhostMemoryMoves m,
      if h : GiantSignedGhostBatchFits H r then F ⟨r,h⟩ else 0) =
      ∑ deleted : (∀ g, Finset (Fin (m.1 g))), ∑ b : B → Fin (H+1), ∑ born : ∀ g, Fin (b g).val → P g,
        F (giantSignedGhostFiniteBatchEquiv m H ⟨deleted,b,born⟩) := by
  classical
  let G : Set (GiantSignedGhostMemoryMoves m) := {r | GiantSignedGhostBatchFits H r}
  let F' (r : GiantSignedGhostMemoryMoves m) : R :=
    if h : GiantSignedGhostBatchFits H r then F ⟨r,h⟩ else 0
  have hsub : (∑' r : G, F r) = ∑' r, F' r := by
    calc
      _ = ∑' r : G, F' r.val := tsum_congr (fun r => (dite_eq_left r.property).symm)
      _ = ∑' r, G.indicator F' r := tsum_subtype G F'
      _ = _ := tsum_congr (fun r => by
        by_cases hr : r ∈ G
        · exact Set.indicator_of_mem hr F'
        · have hz : F' r = 0 := dite_eq_right (show ¬ GiantSignedGhostBatchFits H r from hr)
          exact (Set.indicator_of_notMem hr F').trans hz.symm)
  refine hsub.symm.trans (((giantSignedGhostFiniteBatchEquiv m H).tsum_eq F).symm.trans ?_)
  simp only [tsum_fintype, Fintype.sum_sigma]

end
end ArtinMatthews
