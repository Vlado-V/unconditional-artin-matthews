module

public import ArtinMatthews.MarkedMemoryHistoryStages


set_option backward.privateInPublic true
@[expose] public section

/-! Consequences of the actual global birth-distinct condition, only after
imposing the empty initial pending-memory boundary. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryEmptyPopulationEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0) :
    MarkedMemoryPopulationIndex s ≃ (Σ _j : J, Fin M) where
  toFun := Sum.elim id (fun i => False.elim (by have h := i.2.isLt; have hz := hempty i.1; omega))
  invFun := Sum.inl
  left_inv := by
    intro i
    rcases i with active | ⟨j,k⟩
    · rfl
    · have h := k.isLt
      have hz := hempty j
      omega
  right_inv := by intro i; rfl

theorem markedMemoryEmptyPopulationEquiv_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (i : MarkedMemoryPopulationIndex s) :
    (s.2.1 (markedMemoryEmptyPopulationEquiv s hempty i).1
      (markedMemoryEmptyPopulationEquiv s hempty i).2).1 = markedMemoryPopulationPrime s i := by
  rcases i with active | ⟨j,k⟩
  · rfl
  · have h := k.isLt
    have hz := hempty j
    omega

/-- A literal stage particle is assigned an initial-active or performed-birth address. -/
def markedMemoryHistoryStageBirthOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (t : MarkedMemoryHistoryStage n) :
    MarkedMemoryPopulationIndex (markedMemoryHistoryStageState hZ history t) ↪
      ((Σ _j : J, Fin (pads+1)) ⊕ MarkedMemoryHistoryBirths hZ history) :=
  (markedMemoryHistoryStageOrigin hZ history t).trans
    (Function.Embedding.sumMap (markedMemoryEmptyPopulationEquiv s hempty).toEmbedding
      (Function.Embedding.refl _))

theorem markedMemoryHistoryStageBirthOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (t : MarkedMemoryHistoryStage n)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryStageState hZ history t)) :
    Sum.elim (fun a : Σ _j : J, Fin (pads+1) => (s.2.1 a.1 a.2).1)
      (markedMemoryHistoryBirthPrime hZ history) (markedMemoryHistoryStageBirthOrigin hZ history hempty t i) =
        markedMemoryPopulationPrime (markedMemoryHistoryStageState hZ history t) i := by
  have h := markedMemoryHistoryStageOrigin_prime hZ history t i
  change Sum.elim _ _ (Sum.map (markedMemoryEmptyPopulationEquiv s hempty) id
    (markedMemoryHistoryStageOrigin hZ history t i)) = _
  generalize ho : markedMemoryHistoryStageOrigin hZ history t i = o at h ⊢
  cases o with
  | inl old => exact (markedMemoryEmptyPopulationEquiv_prime s hempty old).trans h
  | inr birth => exact h

/-- Global distinctness of actual birth values forces every intermediate
population to have distinct prime values. No pointwise state bound is assumed. -/
theorem markedMemoryHistoryBirthDistinct_stage {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (t : MarkedMemoryHistoryStage n) :
    Function.Injective (markedMemoryPopulationPrime (markedMemoryHistoryStageState hZ history t)) := by
  intro i j hij
  apply (markedMemoryHistoryStageBirthOrigin hZ history hempty t).injective
  apply hd
  simpa only [markedMemoryHistoryStageBirthOrigin_prime] using hij

/-- Under the stated global condition, equal prime marks at different stages
mean the same actual birth identity, including pending visits. -/
theorem markedMemoryHistoryBirthDistinct_same_origin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (t u : MarkedMemoryHistoryStage n)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryStageState hZ history t))
    (j : MarkedMemoryPopulationIndex (markedMemoryHistoryStageState hZ history u)) :
    markedMemoryPopulationPrime (markedMemoryHistoryStageState hZ history t) i =
        markedMemoryPopulationPrime (markedMemoryHistoryStageState hZ history u) j ↔
      markedMemoryHistoryStageBirthOrigin hZ history hempty t i =
        markedMemoryHistoryStageBirthOrigin hZ history hempty u j := by
  constructor
  · intro h
    apply hd
    simpa only [markedMemoryHistoryStageBirthOrigin_prime] using h
  · intro h
    have hm := congrArg (Sum.elim (fun a : Σ _j : J, Fin (pads+1) => (s.2.1 a.1 a.2).1)
      (markedMemoryHistoryBirthPrime hZ history)) h
    simpa only [markedMemoryHistoryStageBirthOrigin_prime] using hm

end
end ArtinMatthews
