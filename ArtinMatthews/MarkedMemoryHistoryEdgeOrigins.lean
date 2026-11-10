module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPopulation
public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsIndices
public import ArtinMatthews.MarkedMemoryHistoryOrigins
public import ArtinMatthews.MarkedMinorArcRawEdgeState
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual canonical edge population injects into its indexed old population plus exactly
the performed fresh births. Stores preserve an old active identity; they create no new identity. -/
namespace ArtinMatthews
noncomputable section

/-- Reinterpret the actual survivor set as the complement of the selected old promotion. -/
def markedMemoryEdgeSurvivorEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (j : J) :
    ↥(markedRawGhostSurvivors m (markedRawEdgePromotionDeletion prom) j) ≃
      {i : Fin (m.1.1 j : ℕ) // i ∉ (prom j).toFinset} :=
  Equiv.subtypeEquivRight (fun _ => by simp [markedRawGhostSurvivors, markedRawEdgePromotionDeletion])

/-- Split one actual target group's indices into copied, last, surviving, and stored slots. -/
def markedMemoryEdgeGroupSplit {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) :
    (Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) ≃
      ((Fin pads ⊕ Fin 1) ⊕
        ({i : Fin (s.2.2.1.1 j : ℕ) // i ∉ (choice.promotions j).toFinset} ⊕
          Fin (if choice.store j then 1 else 0))) :=
  Equiv.sumCongr finSumFinEquiv.symm
    ((markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
      (markedRawEdgeStoreSizes hZ s choice) j).trans
      (Equiv.sumCongr (markedMemoryEdgeSurvivorEquiv s.2.2 choice.promotions j) (Equiv.refl _)))

/-- The genuine one-group old-or-fresh origin injection. -/
def markedMemoryEdgeGroupOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) :
    (Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) ↪
      ((Fin (pads+1) ⊕ Fin (s.2.2.1.1 j : ℕ)) ⊕ PLift (choice.promotions j = none)) :=
  (markedMemoryEdgeGroupSplit hZ s choice j).toEmbedding.trans
    ((markedMemoryEdgeSplitOrigin (choice.promotions j)
      (by cases choice.store j <;> simp)).trans
      (Equiv.sumCongr (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)) (Equiv.refl _)).toEmbedding)

/-- A plain-function computation rule for the actual grouped origin injection. -/
theorem markedMemoryEdgeGroupOrigin_apply {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J)
    (i : Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) :
    markedMemoryEdgeGroupOrigin hZ s choice j i =
      Sum.map (Sum.map (finSumFinEquiv : Fin pads ⊕ Fin 1 ≃ Fin (pads+1)) id) id
        (markedMemoryEdgeSplitOriginFn (choice.promotions j)
          (Sum.map finSumFinEquiv.symm
            (fun k => Sum.map (markedMemoryEdgeSurvivorEquiv s.2.2 choice.promotions j) id
              (markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
                (markedRawEdgeStoreSizes hZ s choice) j k)) i)) := rfl

/-- The exact canonical edge injection, with one fresh address only in an unpromoted group. -/
def markedMemoryEdgePopulationOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s choice) ↪
      (MarkedMemoryPopulationIndex s ⊕ {j : J // choice.promotions j = none}) :=
  (markedMemoryPopulationGroupEquiv (markedRawEdgeTargetState hZ s choice)).toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl J)
      (markedMemoryEdgeGroupOrigin hZ s choice)).trans
      ((Equiv.sigmaSumDistrib
        (fun j => Fin (pads+1) ⊕ Fin (s.2.2.1.1 j : ℕ))
        (fun j => PLift (choice.promotions j = none))).toEmbedding.trans
        (Equiv.sumCongr (markedMemoryPopulationGroupEquiv s).symm
          (Equiv.sigmaPLiftEquivSubtype (fun j => choice.promotions j = none))).toEmbedding))

/-- Distinct target population indices never duplicate an old or performed fresh identity. -/
theorem markedMemoryEdgePopulationOrigin_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    Function.Injective (markedMemoryEdgePopulationOrigin hZ s choice) :=
  (markedMemoryEdgePopulationOrigin hZ s choice).injective

@[simp] theorem markedMemoryEdgeGroupOrigin_copied {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (i : Fin pads) :
    markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i.castSucc) =
      Sum.inl (Sum.inl i.castSucc) := by
  rw [markedMemoryEdgeGroupOrigin_apply]
  dsimp only [markedRawEdgeTargetMemory, markedRawGhostTargetMemory]
  simp only [Sum.map_inl, finSumFinEquiv_symm_apply_castSucc,
    markedMemoryEdgeSplitOriginFn_copied, finSumFinEquiv_apply_left]
  rfl

@[simp] theorem markedMemoryEdgeGroupOrigin_survivor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J)
    (i : ↥(markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion choice.promotions) j)) :
    markedMemoryEdgeGroupOrigin hZ s choice j
      (Sum.inr ((markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
        (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inl i))) =
      Sum.inl (Sum.inr i.1) := by
  rw [markedMemoryEdgeGroupOrigin_apply]
  dsimp only [markedRawEdgeTargetMemory, markedRawGhostTargetMemory]
  simp [markedMemoryEdgeSurvivorEquiv]

@[simp] theorem markedMemoryEdgeGroupOrigin_store {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (i : Fin ((markedRawEdgeStoreSizes hZ s choice).1 j : ℕ)) :
    markedMemoryEdgeGroupOrigin hZ s choice j
      (Sum.inr ((markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
        (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inr i))) =
      Sum.inl (Sum.inl (Fin.last pads)) := by
  rw [markedMemoryEdgeGroupOrigin_apply]
  dsimp only [markedRawEdgeTargetMemory, markedRawGhostTargetMemory]
  simp only [Sum.map_inr, Equiv.apply_symm_apply, id_eq,
    markedMemoryEdgeSplitOriginFn_store, Sum.map_inl, finSumFinEquiv_apply_right]
  rfl

@[simp] theorem markedMemoryEdgeGroupOrigin_last_none {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (hn : choice.promotions j = none) :
    markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl (Fin.last pads)) = Sum.inr ⟨hn⟩ := by
  rw [markedMemoryEdgeGroupOrigin_apply]
  dsimp only [markedRawEdgeTargetMemory, markedRawGhostTargetMemory]
  simp only [Sum.map_inl, finSumFinEquiv_symm_last,
    markedMemoryEdgeSplitOriginFn_none _ hn, Sum.map_inr, id_eq]

@[simp] theorem markedMemoryEdgeGroupOrigin_last_some {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (k : Fin (s.2.2.1.1 j : ℕ))
    (hk : choice.promotions j = some k) :
    markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl (Fin.last pads)) =
      Sum.inl (Sum.inr k) := by
  rw [markedMemoryEdgeGroupOrigin_apply]
  dsimp only [markedRawEdgeTargetMemory, markedRawGhostTargetMemory]
  simp only [Sum.map_inl, finSumFinEquiv_symm_last,
    markedMemoryEdgeSplitOriginFn_some _ _ hk, Sum.map_inr, id_eq]

/-- Prime labels in a group reassociation of the literal population. -/
def markedMemoryPopulationGroupPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (j : J) :
    (Fin M ⊕ Fin (s.2.2.1.1 j : ℕ)) → Nat.Primes :=
  Sum.elim (fun i => (s.2.1 j i).1) (fun i => (s.2.2.2 j i).1.1)

/-- Every one-group origin carries exactly the target's actual prime value. -/
theorem markedMemoryEdgeGroupOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J)
    (i : Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) :
    Sum.elim (markedMemoryPopulationGroupPrime s j)
      (fun _ : PLift (choice.promotions j = none) =>
        (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1)
      (markedMemoryEdgeGroupOrigin hZ s choice j i) =
    markedMemoryPopulationGroupPrime (markedRawEdgeTargetState hZ s choice) j i := by
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun k => ?_) i
    · by_cases h : choice.promotions j = none
      · rw [markedMemoryEdgeGroupOrigin_last_none hZ s choice j h]
        simp [markedMemoryPopulationGroupPrime, markedRawEdgeTargetState, markedRawActiveSplit]
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
        rw [markedMemoryEdgeGroupOrigin_last_some hZ s choice j k hk]
        simp [markedMemoryPopulationGroupPrime, markedRawEdgeTargetState, markedRawActiveSplit,
          markedRawEdgeTargetLast_promoted s.2.2 choice.promotions choice.fresh j k hk]
    · rw [markedMemoryEdgeGroupOrigin_copied]
      simp [markedMemoryPopulationGroupPrime, markedRawEdgeTargetState, markedRawActiveSplit]
  · obtain ⟨v, rfl⟩ := (markedMemoryGhostOrigin s.2.2
      (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice) j).symm.surjective i
    cases v with
    | inl old =>
      rw [markedMemoryEdgeGroupOrigin_survivor]
      change (s.2.2.2 j old.1).1.1 =
        ((markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2)
          (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice)
          (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j)).2 j
          ((markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
            (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inl old))).1.1
      rw [markedMemoryGhostOrigin_old]
    | inr stored =>
      rw [markedMemoryEdgeGroupOrigin_store]
      change (s.2.1 j (Fin.last pads)).1 =
        ((markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2)
          (markedRawEdgePromotionDeletion choice.promotions) (markedRawEdgeStoreSizes hZ s choice)
          (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j)).2 j
          ((markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion choice.promotions)
            (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inr stored))).1.1
      rw [markedMemoryGhostOrigin_birth]
      rfl

end
end ArtinMatthews
