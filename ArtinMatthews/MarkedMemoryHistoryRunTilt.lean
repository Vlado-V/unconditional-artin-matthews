module

public import ArtinMatthews.MarkedMemoryHistoryRunPowers
public import ArtinMatthews.MarkedMemoryTiltBasic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual grouped nu/V factor of each performed birth has exactly
the original inverse-V charge for every active run, together with one
uniform projective-line factor and one baseline denominator. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (V : J → ℝ) (hV : ∀ j, V j ≠ 0) (q : ℝ) (N : ℕ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

include hV

/-- A ghost-born identity contributes V nu and no initial active-run
charge; a fresh edge birth contributes nu and its initial active-run
charge. Every subsequent actual promotion contributes one more inverse V. -/
theorem markedMemoryHistory_birth_run_charge (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    let a : MarkedMemoryHistoryTraceAddress hZ history := Sum.inr ⟨t,b⟩
    let i := markedMemoryHistoryTraceBirthEquiv hZ history ⟨t,b⟩
    let p := markedMemoryHistoryBirthLabel hZ history i
    markedMemoryHistoryTraceBirthMass
        (fun j p => markedMemoryPrimeAtom (V j) q N (p.1 : ℕ)) V hZ history a *
      markedMemoryHistoryRunMass V hZ history a =
      (V p.1)⁻¹ ^ (if markedMemoryHistoryBirthIsGhost hZ history i then
          markedMemoryHistoryRunCount hZ history a else markedMemoryHistoryRunCount hZ history a+1) *
        (1 / ((((p.2.1 : ℕ) : ℝ)+1)*markedMemoryBaseline q N (p.2.1 : ℕ))) := by
  dsimp only
  rw [markedMemoryHistoryRunMass_pow]
  let i := markedMemoryHistoryTraceBirthEquiv hZ history ⟨t,b⟩
  let p := markedMemoryHistoryBirthLabel hZ history i
  let r := markedMemoryHistoryRunCount hZ history (Sum.inr ⟨t,b⟩)
  change ((if markedMemoryHistoryBirthIsGhost hZ history i then V p.1 else 1) *
      markedMemoryPrimeAtom (V p.1) q N (p.2.1 : ℕ)) * (V p.1)⁻¹ ^ r =
    (V p.1)⁻¹ ^ (if markedMemoryHistoryBirthIsGhost hZ history i then r else r+1) *
      (1 / ((((p.2.1 : ℕ) : ℝ)+1)*markedMemoryBaseline q N (p.2.1 : ℕ)))
  cases hg : markedMemoryHistoryBirthIsGhost hZ history i with
  | false =>
    simpa only [hg, Bool.false_eq_true, ite_false, one_mul] using
      markedMemory_active_run_charge (V p.1) q N (p.2.1 : ℕ) r
  | true =>
    simpa only [hg, Bool.true_eq, ite_true] using
      markedMemory_ghost_run_charge (hV p.1) q N (p.2.1 : ℕ) r

end
end ArtinMatthews
