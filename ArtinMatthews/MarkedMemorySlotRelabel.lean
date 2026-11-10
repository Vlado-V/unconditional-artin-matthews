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

/-! Copied-slot matching is natural under a genuine identity equivalence.
The source and target slot permutations for a fixed free copied order
remain exactly the same permutations. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} {pads : ℕ} (e : A ≃ B)
  (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))

def markedMemorySlotFiberRelabel : MarkedMemorySlotPairFiber src dst out inc ≃
    MarkedMemorySlotPairFiber (src.trans e.toEmbedding) (dst.trans e.toEmbedding) out inc where
  toFun pair := ⟨pair.1,⟨pair.2.1,pair.2.2.1,fun k => congrArg e (pair.2.2.2 k)⟩⟩
  invFun pair := ⟨pair.1,⟨pair.2.1,pair.2.2.1,fun k => e.injective (pair.2.2.2 k)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
theorem markedMemoryBirthBatch_relabel :
    markedMemoryBirthBatch (src.trans e.toEmbedding) = (markedMemoryBirthBatch src).map e.toEmbedding := by
  simp only [markedMemoryBirthBatch, Finset.map_map]

theorem markedMemoryRelabel_remaining
    (h : (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc)) :
    (markedMemoryBirthBatch (src.trans e.toEmbedding)).erase (e (src out)) =
      (markedMemoryBirthBatch (dst.trans e.toEmbedding)).erase (e (dst inc)) := by
  rw [markedMemoryBirthBatch_relabel, markedMemoryBirthBatch_relabel]
  exact (Finset.map_erase e.toEmbedding (markedMemoryBirthBatch src) (src out)).symm.trans
    ((congrArg (fun q => q.map e.toEmbedding) h).trans
      (Finset.map_erase e.toEmbedding (markedMemoryBirthBatch dst) (dst inc)))

theorem markedMemoryRemainingSlotMatching_relabel
    (h : (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc)) :
    markedMemoryRemainingSlotMatching (src.trans e.toEmbedding) (dst.trans e.toEmbedding) out inc
      (markedMemoryRelabel_remaining e src dst out inc h) =
        markedMemoryRemainingSlotMatching src dst out inc h := by
  symm
  apply markedMemoryRemainingSlotMatching_unique
  intro k
  exact congrArg e (markedMemoryRemainingSlotMatching_apply src dst out inc h k)

theorem markedMemorySlotPairOfOrder_relabel
    (h : (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc))
    (order : Equiv.Perm (Fin pads)) :
    markedMemorySlotPairOfOrder (src.trans e.toEmbedding) (dst.trans e.toEmbedding) out inc
      (markedMemoryRelabel_remaining e src dst out inc h) order =
        markedMemorySlotPairOfOrder src dst out inc h order := by
  unfold markedMemorySlotPairOfOrder
  rw [markedMemoryRemainingSlotMatching_relabel]

theorem markedMemorySlotFiberOfOrder_relabel
    (h : (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc))
    (order : Equiv.Perm (Fin pads)) :
    (markedMemorySlotFiberRelabel e src dst out inc)
        (markedMemorySlotFiberOfOrder src dst out inc h order) =
      markedMemorySlotFiberOfOrder (src.trans e.toEmbedding) (dst.trans e.toEmbedding) out inc
        (markedMemoryRelabel_remaining e src dst out inc h) order := by
  apply Subtype.ext
  exact (markedMemorySlotPairOfOrder_relabel e src dst out inc h order).symm

theorem markedMemorySlotPairOfOrder_congr_indices
    (out' inc' : Fin (pads+1)) (ho : out = out') (hi : inc = inc')
    (h : (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc))
    (h' : (markedMemoryBirthBatch src).erase (src out') = (markedMemoryBirthBatch dst).erase (dst inc'))
    (order : Equiv.Perm (Fin pads)) :
    markedMemorySlotPairOfOrder src dst out inc h order =
      markedMemorySlotPairOfOrder src dst out' inc' h' order := by
  subst out'
  subst inc'
  rfl

end
end ArtinMatthews
