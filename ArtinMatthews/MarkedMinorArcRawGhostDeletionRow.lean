module

public import ArtinMatthews.MarkedMinorArcRawGhostBirthRow


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite eligible-deletion sum in the actual signed ghost row.
Every choice is an old index; repeated particle values remain distinct. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Summing actual eligible indexed masks is the literal binomial
survival/deletion factor, before any operator inequality. -/
theorem markedRawGhost_all_mask_sum {k : ℕ} (H : Finset (Fin k)) (a b : ℝ) :
    (∑ del : Finset (Fin k), if del ⊆ H then a^del.card*b^(H \ del).card else 0)=(a+b)^H.card := by
  classical
  have hs : (Finset.univ : Finset (Finset (Fin k))).filter (fun del => del ⊆ H)=H.powerset := by
    ext del
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powerset]
  rw [← Finset.sum_filter,hs,markedRawGhost_deletion_polynomial]

/-- The independent group eligibility factors are exactly the actual
simultaneous old-hit deletion rule; no mask-count upper bound is used. -/
theorem markedRawGhost_eligible_product {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m) (A : J → ℝ) :
    (∏ j, if del j ⊆ markedRawGroupHitIndices m j z hz then A j else 0)=
      if MarkedRawGhostDeletionAllowed m z hz del then ∏ j, A j else 0 := by
  classical
  by_cases h : MarkedRawGhostDeletionAllowed m z hz del
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro j _
    exact ite_eq_left (h j)
  · rw [ite_eq_right h]
    change ¬∀ j, del j ⊆ markedRawGroupHitIndices m j z hz at h
    obtain ⟨j,hj⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- The actual full deletion sum factors into the exact source survival
polynomial for every group, with no 2^B or pending-degree loss. -/
theorem markedRawGhost_deletion_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (qStage ρ v₀ : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    (∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
      ∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j else 0)=
      ∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card := by
  classical
  calc
    _ = ∑ del : MarkedRawGhostDeletion m,
        ∏ j, if del j ⊆ markedRawGroupHitIndices m j z hz then
          markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j else 0 := by
      apply Finset.sum_congr rfl
      intro del _
      exact (markedRawGhost_eligible_product m z hz del _).symm
    _ = ∏ j, ∑ D : Finset (Fin (m.1.1 j : ℕ)),
        if D ⊆ markedRawGroupHitIndices m j z hz then
          ((1-qStage)/(ρ*v₀))^D.card*(qStage/ρ^2)^(markedRawGroupHitIndices m j z hz \ D).card else 0 :=
      (Fintype.prod_sum (fun j (D : Finset (Fin (m.1.1 j : ℕ))) =>
        if D ⊆ markedRawGroupHitIndices m j z hz then
          ((1-qStage)/(ρ*v₀))^D.card*(qStage/ρ^2)^(markedRawGroupHitIndices m j z hz \ D).card else 0)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rw [markedRawGhost_all_mask_sum,add_comm]

end ArtinMatthews
