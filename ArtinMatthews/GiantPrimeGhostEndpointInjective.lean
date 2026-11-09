module

public import ArtinMatthews.GiantPrimeLifespanInverse
public import ArtinMatthews.GiantPrimeLifespanStatus


set_option backward.privateInPublic true
@[expose] public section

/-! The ghost birth and death visits determine the original lifespan choice. -/

namespace ArtinMatthews

variable {n : ℕ} {A : Finset (Fin n)}

private theorem lifespanView_none_of_ghostBirth_iff
    (c d : GiantSignedResidueLifespanChoice A)
    (hc : giantSignedPrimeLifespanView A c = none)
    (hB : ∀ i, giantSignedPrimeGhostBirthAt c i ↔ giantSignedPrimeGhostBirthAt d i) :
    giantSignedPrimeLifespanView A d = none := by
  cases hd : giantSignedPrimeLifespanView A d with
  | none => rfl
  | some R =>
    have hA := giantSignedPrimeLifespanView_none_empty A c hc
    have hBirth : giantSignedPrimeGhostBirthAt d R.start := by
      rw [giantSignedPrimeGhostBirthAt, hd, Option.elim_some]
      exact ⟨rfl, R.ghostBirth_iff.mpr (by simp [hA])⟩
    have h := (hB R.start).mpr hBirth
    exact False.elim (by simpa only [giantSignedPrimeGhostBirthAt, hc, Option.elim_none] using h)

/-- For fixed active visits, equality of the actual ghost birth and death statuses
recovers the finite choice, including absence and strict orphans. -/
theorem giantSignedResidueLifespanChoice_eq_of_ghostEndpoints
    (c d : GiantSignedResidueLifespanChoice A)
    (hB : ∀ i, giantSignedPrimeGhostBirthAt c i ↔ giantSignedPrimeGhostBirthAt d i)
    (hD : ∀ i, giantSignedPrimeGhostDeathAt c i ↔ giantSignedPrimeGhostDeathAt d i) :
    c = d := by
  apply giantSignedPrimeLifespanView_injective A
  cases hc : giantSignedPrimeLifespanView A c with
  | none => exact (lifespanView_none_of_ghostBirth_iff c d hc hB).symm
  | some L =>
    cases hd : giantSignedPrimeLifespanView A d with
    | none =>
      exact hc.symm.trans (lifespanView_none_of_ghostBirth_iff d c hd (fun i => (hB i).symm))
    | some R =>
      apply congrArg some
      apply giantSignedPrimeLifespanInterval_ext
      · have hStart (i : Fin n) : (L.start = i ∧ L.ghostBirth = true) ↔
            (R.start = i ∧ R.ghostBirth = true) := by
          simpa only [giantSignedPrimeGhostBirthAt, hc, hd, Option.elim_some] using hB i
        by_cases hL : L.ghostBirth = true
        · exact ((hStart L.start).mp ⟨rfl, hL⟩).1.symm
        · have hR : ¬R.ghostBirth = true := fun h => hL ((hStart R.start).mpr ⟨rfl, h⟩).2
          have hl : L.start ∈ A := by by_contra hn; exact hL (L.ghostBirth_iff.mpr hn)
          have hr : R.start ∈ A := by by_contra hn; exact hR (R.ghostBirth_iff.mpr hn)
          exact le_antisymm (L.active_contained _ hr).1 (R.active_contained _ hl).1
      · have hFinish (i : Fin n) : (L.finish = i ∧ L.ghostDeath = true) ↔
            (R.finish = i ∧ R.ghostDeath = true) := by
          simpa only [giantSignedPrimeGhostDeathAt, hc, hd, Option.elim_some] using hD i
        by_cases hL : L.ghostDeath = true
        · exact ((hFinish L.finish).mp ⟨rfl, hL⟩).1.symm
        · have hR : ¬R.ghostDeath = true := fun h => hL ((hFinish R.finish).mpr ⟨rfl, h⟩).2
          have hl : L.finish ∈ A := by by_contra hn; exact hL (L.ghostDeath_iff.mpr hn)
          have hr : R.finish ∈ A := by by_contra hn; exact hR (R.ghostDeath_iff.mpr hn)
          exact le_antisymm (R.active_contained _ hl).2 (L.active_contained _ hr).2

end ArtinMatthews
