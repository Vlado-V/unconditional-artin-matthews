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

/-! Exact mass of the compatible source/target slot-pair fiber. The two
inverse permutation-cardinality factors are retained separately before
the actual fiber cardinality is inserted. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryRemainingIdentityRange {A : Type*} {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (out : Fin (pads+1)) : Set A :=
  {a | ∃ i, i ≠ out ∧ src i = a}

theorem markedMemoryRemainingIdentityRange_mem {A : Type*} [DecidableEq A] {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (out : Fin (pads+1)) (a : A) :
    a ∈ markedMemoryRemainingIdentityRange src out ↔
      a ∈ (markedMemoryBirthBatch src).erase (src out) := by
  simp only [markedMemoryRemainingIdentityRange, Set.mem_ofPred_eq, Finset.mem_erase,
    markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,hi,hia⟩
    refine ⟨?_, i, hia⟩
    intro ha
    exact hi (src.injective (hia.trans ha))
  · rintro ⟨ha,i,hia⟩
    refine ⟨i,?_,hia⟩
    intro hi
    exact ha (hia.symm.trans (congrArg src hi))

theorem markedMemoryRemainingIdentityRange_eq_iff {A : Type*} [DecidableEq A] {pads : ℕ}
    (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1)) :
    markedMemoryRemainingIdentityRange src out = markedMemoryRemainingIdentityRange dst inc ↔
      (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc) := by
  constructor
  · intro h
    apply Finset.ext
    intro a
    rw [← markedMemoryRemainingIdentityRange_mem, ← markedMemoryRemainingIdentityRange_mem, h]
  · intro h
    apply Set.ext
    intro a
    rw [markedMemoryRemainingIdentityRange_mem, markedMemoryRemainingIdentityRange_mem, h]

theorem markedMemorySlotPairCompatible_remaining {A : Type*} [DecidableEq A] {pads : ℕ}
    (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
    (pair : Equiv.Perm (Fin (pads+1)) × Equiv.Perm (Fin (pads+1)))
    (hp : MarkedMemorySlotPairCompatible src dst out inc pair) :
    (markedMemoryBirthBatch src).erase (src out) = (markedMemoryBirthBatch dst).erase (dst inc) := by
  have ht : pair.2.symm (Fin.last pads) = inc := by
    apply pair.2.injective
    rw [Equiv.apply_symm_apply, hp.2.1]
  have he : markedMemoryCopiedSlotEmbedding src pair.1 = markedMemoryCopiedSlotEmbedding dst pair.2.symm := by
    apply Function.Embedding.ext
    intro k
    exact hp.2.2 k
  exact (markedMemoryCopiedSlotEmbedding_batch src pair.1 out hp.1).symm.trans
    ((congrArg markedMemoryBirthBatch he).trans
      (markedMemoryCopiedSlotEmbedding_batch dst pair.2.symm inc ht))

variable {A : Type*} [DecidableEq A] {pads : ℕ}
  (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
  (hremaining : (markedMemoryBirthBatch src).erase (src out) =
    (markedMemoryBirthBatch dst).erase (dst inc))

include hremaining

/-- The true fiber count multiplies both original slot probabilities. -/
theorem markedMemorySlotPair_normalized_sum (c : ℂ) :
    (∑ _pair : MarkedMemorySlotPairFiber src dst out inc,
      (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ * c *
        (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹) =
      (pads.factorial : ℂ) / (((pads+1).factorial : ℂ)^2) * c := by
  rw [Finset.sum_const, Finset.card_univ, markedMemorySlotPairFiber_card src dst out inc hremaining,
    nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  simp only [div_eq_mul_inv]
  ring

theorem markedMemorySlotPair_normalized_mass :
    (∑ _pair : MarkedMemorySlotPairFiber src dst out inc,
      (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℝ)⁻¹ *
        (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℝ)⁻¹) =
      (pads.factorial : ℝ) / (((pads+1).factorial : ℝ)^2) := by
  rw [Finset.sum_const, Finset.card_univ, markedMemorySlotPairFiber_card src dst out inc hremaining,
    nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  simp only [div_eq_mul_inv]
  ring

theorem markedMemorySlotPair_normalized_double_sum (c : ℂ) :
    (∑ σ : Equiv.Perm (Fin (pads+1)), ∑ τ : Equiv.Perm (Fin (pads+1)),
      if MarkedMemorySlotPairCompatible src dst out inc (σ,τ) then
        (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ * c *
          (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ else 0) =
      (pads.factorial : ℂ) / (((pads+1).factorial : ℂ)^2) * c := by
  let f : Equiv.Perm (Fin (pads+1)) × Equiv.Perm (Fin (pads+1)) → ℂ := fun pair =>
    if MarkedMemorySlotPairCompatible src dst out inc pair then
      (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ * c *
        (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ else 0
  change (∑ σ, ∑ τ, f (σ,τ)) = _
  rw [← Fintype.sum_prod_type f]
  dsimp only [f]
  rw [← Finset.sum_filter]
  calc
    _ = ∑ _pair : MarkedMemorySlotPairFiber src dst out inc,
        (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ * c *
          (Fintype.card (Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := markedMemorySlotPair_normalized_sum src dst out inc hremaining c

omit hremaining in
def markedMemorySlotPairFiberEquiv_of_range
    (hrange : markedMemoryRemainingIdentityRange src out = markedMemoryRemainingIdentityRange dst inc) :
    MarkedMemorySlotPairFiber src dst out inc ≃ Equiv.Perm (Fin pads) :=
  markedMemorySlotPairFiberEquiv src dst out inc
    ((markedMemoryRemainingIdentityRange_eq_iff src dst out inc).mp hrange)

omit hremaining in
theorem markedMemorySlotPair_exists_of_range
    (hrange : markedMemoryRemainingIdentityRange src out = markedMemoryRemainingIdentityRange dst inc) :
    ∃ σ τ : Equiv.Perm (Fin (pads+1)), σ (Fin.last pads) = out ∧ τ inc = Fin.last pads ∧
      ∀ k : Fin pads, src (σ k.castSucc) = dst (τ.symm k.castSucc) :=
  markedMemorySlotPair_exists src dst out inc
    ((markedMemoryRemainingIdentityRange_eq_iff src dst out inc).mp hrange)

omit hremaining in
theorem markedMemorySlotPairFiber_card_of_range
    (hrange : markedMemoryRemainingIdentityRange src out = markedMemoryRemainingIdentityRange dst inc) :
    Fintype.card (MarkedMemorySlotPairFiber src dst out inc) = pads.factorial :=
  markedMemorySlotPairFiber_card src dst out inc
    ((markedMemoryRemainingIdentityRange_eq_iff src dst out inc).mp hrange)

omit hremaining in
theorem markedMemorySlotPair_exists_iff_range :
    (∃ σ τ : Equiv.Perm (Fin (pads+1)), MarkedMemorySlotPairCompatible src dst out inc (σ,τ)) ↔
      markedMemoryRemainingIdentityRange src out = markedMemoryRemainingIdentityRange dst inc := by
  constructor
  · rintro ⟨σ,τ,hp⟩
    exact (markedMemoryRemainingIdentityRange_eq_iff src dst out inc).mpr
      (markedMemorySlotPairCompatible_remaining src dst out inc (σ,τ) hp)
  · intro hrange
    exact markedMemorySlotPair_exists_of_range src dst out inc hrange

end
end ArtinMatthews
