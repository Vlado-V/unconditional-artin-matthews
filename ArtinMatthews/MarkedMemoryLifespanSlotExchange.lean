module

public import ArtinMatthews.MarkedMemoryLifespanSlotFiber
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Recover the common survivor set from an actual active-set exchange.
The matching premise of the slot fiber is derived using the equal finite
sizes of the two injected active lists. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A : Type*} [DecidableEq A] {pads : ℕ}
  (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
  (hexchange : ∀ a, (∃ i, dst i = a) ↔
    ((∃ i, src i = a) ∧ a ≠ src out) ∨ a = dst inc)

include hexchange

theorem markedMemoryActiveExchange_batch :
    markedMemoryBirthBatch dst =
      insert (dst inc) ((markedMemoryBirthBatch src).erase (src out)) := by
  ext a
  simp only [markedMemoryBirthBatch, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_map, Finset.mem_univ, true_and]
  have h := hexchange a
  tauto

/-- The incoming identity cannot already be a surviving source identity:
otherwise the target list would have one fewer distinct identity. -/
theorem markedMemoryActiveExchange_incoming_not_remaining :
    dst inc ∉ (markedMemoryBirthBatch src).erase (src out) := by
  have hout : src out ∈ markedMemoryBirthBatch src := by
    simp only [markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨out, rfl⟩
  have hcard : ((markedMemoryBirthBatch src).erase (src out)).card = pads := by
    rw [Finset.card_erase_of_mem hout, markedMemoryBirthBatch_card]
    omega
  intro hin
  have hb := markedMemoryActiveExchange_batch src dst out inc hexchange
  rw [Finset.insert_eq_of_mem hin] at hb
  have hc := congrArg Finset.card hb
  rw [markedMemoryBirthBatch_card, hcard] at hc
  omega

theorem markedMemoryActiveExchange_remaining :
    (markedMemoryBirthBatch src).erase (src out) =
      (markedMemoryBirthBatch dst).erase (dst inc) := by
  rw [markedMemoryActiveExchange_batch src dst out inc hexchange]
  rw [Finset.erase_insert
    (markedMemoryActiveExchange_incoming_not_remaining src dst out inc hexchange)]

theorem markedMemoryActiveExchange_incoming_not_source (hne : src out ≠ dst inc) :
    ¬ ∃ i, src i = dst inc := by
  rintro ⟨i, hi⟩
  apply markedMemoryActiveExchange_incoming_not_remaining src dst out inc hexchange
  apply Finset.mem_erase.mpr
  refine ⟨hne.symm, ?_⟩
  simp only [markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨i, hi⟩

theorem markedMemoryActiveExchange_slotPair_exists :
    ∃ σ τ : Equiv.Perm (Fin (pads+1)),
      MarkedMemorySlotPairCompatible src dst out inc (σ,τ) :=
  markedMemorySlotPair_exists src dst out inc
    (markedMemoryActiveExchange_remaining src dst out inc hexchange)

theorem markedMemoryActiveExchange_slotPair_card :
    Fintype.card (MarkedMemorySlotPairFiber src dst out inc) = pads.factorial :=
  markedMemorySlotPairFiber_card src dst out inc
    (markedMemoryActiveExchange_remaining src dst out inc hexchange)

end
end ArtinMatthews
