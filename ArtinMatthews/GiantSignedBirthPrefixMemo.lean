module

public import ArtinMatthews.GiantSignedBirthConditionalValues
public import ArtinMatthews.GiantSignedBirthStageDraws


set_option backward.privateInPublic true
@[expose] public section

/-! The retained prefix memo agrees with the actual performed values,
including the precise absent addresses at each stage. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def giantSignedBirthOptionPrime : Option ℕ → Option Nat.Primes
  | none => none
  | some p => if hp : p.Prime then some ⟨p,hp⟩ else none

theorem giantSignedBirthOptionPrime_some {p : ℕ} (hp : p.Prime) :
    giantSignedBirthOptionPrime (some p) = some ⟨p,hp⟩ := by
  simp [giantSignedBirthOptionPrime, hp]

variable {B : Type*} [Fintype B] {PB : B → Finset ℕ} {k ell n H : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedUniformBirthPrefixMemo (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (t : ℕ)
    (a : GiantSignedUniformBirthAddress B (k+ell) n H) : Option Nat.Primes :=
  if giantSignedUniformBirthTime a < t then giantSignedBirthOptionPrime
    (giantSignedUniformBirthValue d H hH a) else none

theorem giantSignedUniformBirthPrefixMemo_zero (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) :
    giantSignedUniformBirthPrefixMemo d hH 0 = fun _ => none := by
  funext a
  simp [giantSignedUniformBirthPrefixMemo]

theorem giantSignedUniformBirthPrefixMemo_current_none (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (o : GiantSignedBirthOperation n)
    (a : GiantSignedUniformBirthAddress B (k+ell) n H)
    (ha : giantSignedUniformBirthOperation (k+ell) n H a = o) :
    giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o) a = none := by
  simp [giantSignedUniformBirthPrefixMemo, giantSignedUniformBirthTime, ha]

theorem giantSignedUniformBirthPrefixMemo_step
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (d : GiantSignedBirthData PB ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (o : GiantSignedBirthOperation n) :
    giantSignedUniformBirthConditionalValues hPB (giantSignedBirthStageEmbedding d hH o)
      (giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o))
      (giantSignedBirthStageTuple d hH o) =
      giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o+1) := by
  funext a
  let e := giantSignedBirthStageEmbedding d hH o
  let t := giantSignedBirthOperationTime o
  change giantSignedUniformBirthConditionalValues hPB e (giantSignedUniformBirthPrefixMemo d hH t)
    (giantSignedBirthStageTuple d hH o) a = giantSignedUniformBirthPrefixMemo d hH (t+1) a
  by_cases ha : a ∈ Set.range e
  · obtain ⟨i,rfl⟩ := ha
    have ht : giantSignedUniformBirthTime (e i) = t :=
      congrArg giantSignedBirthOperationTime (giantSignedBirthStageEmbedding_operation d hH o i)
    rw [giantSignedUniformBirthConditionalValues_draw, giantSignedUniformBirthPrefixMemo,
      if_pos (ht.trans_lt (Nat.lt_succ_self _))]
    change _ = giantSignedBirthOptionPrime
      (giantSignedUniformBirthValue d H hH (giantSignedBirthStageEmbedding d hH o i))
    rw [giantSignedBirthStageEmbedding_value, ← giantSignedBirthStageTuple_value d hH o i]
    exact (giantSignedBirthOptionPrime_some (hPB _ _ (giantSignedBirthStageTuple d hH o i).property)).symm
  · rw [giantSignedUniformBirthConditionalValues_outside hPB e _ _ a ha]
    by_cases ht : giantSignedUniformBirthTime a = t
    · have ho : giantSignedUniformBirthOperation (k+ell) n H a = o :=
        giantSignedBirthOperationTime_injective ht
      have hn : giantSignedUniformBirthValue d H hH a = none := by
        by_contra h
        exact ha ((giantSignedBirthStageEmbedding_range d hH o a).mpr ⟨ho,h⟩)
      simp [giantSignedUniformBirthPrefixMemo, ht, hn, giantSignedBirthOptionPrime]
    · have he : giantSignedUniformBirthTime a < t ↔ giantSignedUniformBirthTime a < t+1 := by omega
      unfold giantSignedUniformBirthPrefixMemo
      by_cases hlt : giantSignedUniformBirthTime a < t
      · rw [ite_eq_left hlt, ite_eq_left (he.mp hlt)]
      · rw [ite_eq_right hlt, ite_eq_right (mt he.mpr hlt)]

end
end ArtinMatthews
