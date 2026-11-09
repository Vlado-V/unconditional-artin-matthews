module

public import ArtinMatthews.MarkedMemoryStageWeights
public import ArtinMatthews.MarkedMemoryHistoryEdgeVertices


set_option backward.privateInPublic true
@[expose] public section

/-! The varying-kernel residual is the literal finite product over the
actual chronological edges, with both independent slot probabilities. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψStage : ℕ → SchwartzMap ℝ ℂ) (ηStage : ℕ → ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

theorem markedMemoryStageResidualProduct_vertices (n offset : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n offset H=
      ∏ v : Fin n,markedMemoryEdgeResidual hZ (ψStage (offset+v.val)) (ηStage (offset+v.val))
        d₀ Y Q (χ (offset+v.val))
        (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H v.castSucc))
        (markedMemoryHistoryVertexEdge hZ H v) := by
  induction n generalizing s offset with
  | zero => simp [markedMemoryStageResidualProduct]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change _ * markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n (offset+1) H.2.2=
      _ * ∏ v : Fin n,markedMemoryEdgeResidual hZ (ψStage (offset+(v.val+1)))
        (ηStage (offset+(v.val+1))) d₀ Y Q (χ (offset+(v.val+1)))
        (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ H.2.2 v.castSucc)
          (markedMemoryHistoryVertexGhost hZ H.2.2 v.castSucc))
        (markedMemoryHistoryVertexEdge hZ H.2.2 v)
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    rw [show (offset+1)+v.val=offset+(v.val+1) by omega]

end
end ArtinMatthews
