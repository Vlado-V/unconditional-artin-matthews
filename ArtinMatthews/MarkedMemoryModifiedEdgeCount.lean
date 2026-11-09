module

public import ArtinMatthews.MarkedMemoryBirthPhaseWord


set_option backward.privateInPublic true
@[expose] public section

/-! The mixed word pays the crude edge cost on at most twice the cycle
rank. This counts actual chronological edge operations, not prime values. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedOperatorModifiedEdgeCount (bad : ℕ → Prop) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,j => (if bad j then 1 else 0)+markedOperatorModifiedEdgeCount bad n (j+1)

theorem markedOperatorModifiedEdgeCount_le (bad : ℕ → Prop) (n j : ℕ) :
    markedOperatorModifiedEdgeCount bad n j ≤ n := by
  induction n generalizing j with
  | zero => exact le_rfl
  | succ n ih =>
    have h := ih (j+1)
    unfold markedOperatorModifiedEdgeCount
    split_ifs <;> omega

theorem markedOperatorEdgeBudget_mixed (bad : ℕ → Prop) (R ε : ℝ) (n j : ℕ) :
    markedOperatorEdgeBudget (fun i => if bad i then R else ε) n j =
      ε^(n-markedOperatorModifiedEdgeCount bad n j)*R^(markedOperatorModifiedEdgeCount bad n j) := by
  induction n generalizing j with
  | zero => simp only [markedOperatorEdgeBudget,markedOperatorModifiedEdgeCount,Nat.sub_self,pow_zero,one_mul]
  | succ n ih =>
    have hc := markedOperatorModifiedEdgeCount_le bad n (j+1)
    by_cases hb : bad j
    · simp only [markedOperatorEdgeBudget,markedOperatorModifiedEdgeCount,ite_eq_left hb]
      rw [ih]
      have he : n+1-(1+markedOperatorModifiedEdgeCount bad n (j+1)) =
          n-markedOperatorModifiedEdgeCount bad n (j+1) := by omega
      rw [he]
      simp only [Nat.add_comm 1,pow_succ]
      ring
    · simp only [markedOperatorEdgeBudget,markedOperatorModifiedEdgeCount,ite_eq_right hb,zero_add]
      rw [ih]
      have he : n+1-markedOperatorModifiedEdgeCount bad n (j+1) =
          n-markedOperatorModifiedEdgeCount bad n (j+1)+1 := by omega
      rw [he,pow_succ]
      ring

theorem markedOperatorModifiedEdgeCount_sum (bad : ℕ → Prop) (n j : ℕ) :
    markedOperatorModifiedEdgeCount bad n j = ∑ k ∈ Finset.range n, if bad (j+k) then 1 else 0 := by
  induction n generalizing j with
  | zero => simp [markedOperatorModifiedEdgeCount]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [markedOperatorModifiedEdgeCount,Nat.add_zero]
    rw [ih]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show j+(k+1)=(j+1)+k by omega]

theorem markedMemoryBirth_modified_edges_le_twice_rank
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :
    markedOperatorModifiedEdgeCount (MarkedMemoryBirthEdgeModified σ) N 0 ≤
      2*markedBirthPermutationRank σ := by
  rw [markedOperatorModifiedEdgeCount_sum]
  simp only [Nat.zero_add]
  let T := (Finset.range N).filter (MarkedMemoryBirthEdgeModified σ)
  have hc : (∑ k ∈ Finset.range N, if MarkedMemoryBirthEdgeModified σ k then 1 else 0) = T.card := by
    simp only [T,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hc]
  have hi : T.card ≤ (σ.support.image markedMemoryPotentialOperation).card := by
    apply Finset.card_le_card_of_injOn (fun k : ℕ => some (2*k+1))
    · intro k hk
      exact (Finset.mem_filter.mp hk).2.2
    · intro k _ l _ h
      have hh := Option.some.inj h
      omega
  exact hi.trans (markedMemoryBirth_rank_operation_bound M B N σ)

end ArtinMatthews
