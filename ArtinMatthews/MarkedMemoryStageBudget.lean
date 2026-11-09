module

public import ArtinMatthews.MarkedMemoryBirthStagePivots
public import ArtinMatthews.MarkedWeightedConditionalKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact accumulation of all chronological nonpivot costs. Initial,
ghost and edge stages together contribute precisely the cycle rank. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedMemoryPivotTailCount
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) : ℕ → ℕ → ℕ
  | 0,j => (markedMemoryStageNonpivots σ (2*j+1)).card
  | n+1,j => (markedMemoryStageNonpivots σ (2*j+1)).card+
      (markedMemoryStageNonpivots σ (2*j+2)).card+markedMemoryPivotTailCount σ n (j+1)

theorem markedMemoryPivotTailCount_sum
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (n j : ℕ) :
    markedMemoryPivotTailCount σ n j=
      ∑ k∈Finset.range (2*n+1),(markedMemoryStageNonpivots σ (2*j+1+k)).card := by
  induction n generalizing j with
  | zero => simp [markedMemoryPivotTailCount]
  | succ n ih =>
    let F := fun k => (markedMemoryStageNonpivots σ (2*j+1+k)).card
    have hhead : (∑ k∈Finset.range 2,F k)=F 0+F 1 := by
      simp [Finset.sum_range_succ]
    have htail : (∑ k∈Finset.range (2*n+1),F (2+k))=
        markedMemoryPivotTailCount σ n (j+1) := by
      rw [ih]
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun u => (markedMemoryStageNonpivots σ u).card)
        (show 2*j+1+(2+k)=2*(j+1)+1+k by omega)
    have hsplit := Finset.sum_range_add F 2 (2*n+1)
    rw [hhead] at hsplit
    rw [htail] at hsplit
    simpa only [F,markedMemoryPivotTailCount,Nat.add_zero,
      show 2*j+1+1=2*j+2 by omega,show 2+(2*n+1)=2*(n+1)+1 by omega] using hsplit.symm

theorem markedMemoryPivotTailCount_rank
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :
    (markedMemoryStageNonpivots σ 0).card+markedMemoryPivotTailCount σ N 0=
      markedBirthPermutationRank σ := by
  rw [markedMemoryPivotTailCount_sum]
  calc
    _ = (∑ k∈Finset.range (2*N+1),(markedMemoryStageNonpivots σ (k+1)).card)+
        (markedMemoryStageNonpivots σ 0).card := by
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_comm 1 k]
    _ = ∑ k∈Finset.range (2*N+2),(markedMemoryStageNonpivots σ k).card :=
      (Finset.sum_range_succ' (fun k => (markedMemoryStageNonpivots σ k).card) (2*N+1)).symm
    _ = _ := markedMemoryStageNonpivots_card_sum σ

theorem markedMemory_conditional_budget
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (Δ C R : ℝ) (n j : ℕ) :
    markedConditionalWordBudget
      (fun k => Δ^(markedMemoryStageNonpivots σ (2*k+1)).card*C)
      (fun k => Δ^(markedMemoryStageNonpivots σ (2*k+2)).card*R) n j =
      C^(n+1)*R^n*Δ^(markedMemoryPivotTailCount σ n j) := by
  induction n generalizing j with
  | zero => simp [markedConditionalWordBudget,markedMemoryPivotTailCount,mul_comm]
  | succ n ih =>
    simp only [markedConditionalWordBudget,markedMemoryPivotTailCount,ih]
    rw [pow_add,pow_add,pow_succ C,pow_succ R]
    ring

theorem markedMemory_conditional_budget_initial
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (Δ C R : ℝ) :
    Δ^(markedMemoryStageNonpivots σ 0).card*
      markedConditionalWordBudget
        (fun k => Δ^(markedMemoryStageNonpivots σ (2*k+1)).card*C)
        (fun k => Δ^(markedMemoryStageNonpivots σ (2*k+2)).card*R) N 0 =
      C^(N+1)*R^N*Δ^(markedBirthPermutationRank σ) := by
  rw [markedMemory_conditional_budget]
  calc
    _ = C^(N+1)*R^N*(Δ^(markedMemoryStageNonpivots σ 0).card*Δ^(markedMemoryPivotTailCount σ N 0)) := by ring
    _ = _ := by rw [← pow_add,markedMemoryPivotTailCount_rank]

end ArtinMatthews
