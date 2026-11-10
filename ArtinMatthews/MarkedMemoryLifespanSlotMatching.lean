module

public import ArtinMatthews.MarkedMemoryHistoryBirthPermutations
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

/-! Matching the surviving active identities is derived from equality of
the two remaining identity sets. No equality or injectivity of numeric
prime marks is required. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryExtendSlotPermutation {pads : ℕ} (π : Equiv.Perm (Fin pads)) :
    Equiv.Perm (Fin (pads+1)) where
  toFun := Fin.lastCases (Fin.last pads) (fun k => (π k).castSucc)
  invFun := Fin.lastCases (Fin.last pads) (fun k => (π.symm k).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc, Equiv.symm_apply_apply]
  right_inv i := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc, Equiv.apply_symm_apply]

@[simp] theorem markedMemoryExtendSlotPermutation_last {pads : ℕ} (π : Equiv.Perm (Fin pads)) :
    markedMemoryExtendSlotPermutation π (Fin.last pads) = Fin.last pads := by
  change Fin.lastCases (motive := fun _ : Fin (pads+1) => Fin (pads+1))
    (Fin.last pads) (fun k => (π k).castSucc) (Fin.last pads) = Fin.last pads
  exact Fin.lastCases_last

@[simp] theorem markedMemoryExtendSlotPermutation_castSucc {pads : ℕ}
    (π : Equiv.Perm (Fin pads)) (k : Fin pads) :
    markedMemoryExtendSlotPermutation π k.castSucc = (π k).castSucc := by
  change Fin.lastCases (motive := fun _ : Fin (pads+1) => Fin (pads+1))
    (Fin.last pads) (fun j => (π j).castSucc) k.castSucc = (π k).castSucc
  exact Fin.lastCases_castSucc k

def markedMemoryOutgoingSlotPermutation {pads : ℕ} (out : Fin (pads+1))
    (π : Equiv.Perm (Fin pads)) : Equiv.Perm (Fin (pads+1)) :=
  (markedMemoryExtendSlotPermutation π).trans (Equiv.swap (Fin.last pads) out)

@[simp] theorem markedMemoryOutgoingSlotPermutation_last {pads : ℕ}
    (out : Fin (pads+1)) (π : Equiv.Perm (Fin pads)) :
    markedMemoryOutgoingSlotPermutation out π (Fin.last pads) = out := by
  simp only [markedMemoryOutgoingSlotPermutation, Equiv.trans_apply,
    markedMemoryExtendSlotPermutation_last, Equiv.swap_apply_left]

@[simp] theorem markedMemoryOutgoingSlotPermutation_castSucc {pads : ℕ}
    (out : Fin (pads+1)) (π : Equiv.Perm (Fin pads)) (k : Fin pads) :
    markedMemoryOutgoingSlotPermutation out π k.castSucc =
      Equiv.swap (Fin.last pads) out (π k).castSucc := by
  simp only [markedMemoryOutgoingSlotPermutation, Equiv.trans_apply,
    markedMemoryExtendSlotPermutation_castSucc]

def markedMemoryCopiedSlotEmbedding {A : Type*} {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (σ : Equiv.Perm (Fin (pads+1))) : Fin pads ↪ A :=
  (Fin.castSuccEmb.trans σ.toEmbedding).trans src

@[simp] theorem markedMemoryCopiedSlotEmbedding_apply {A : Type*} {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (σ : Equiv.Perm (Fin (pads+1))) (k : Fin pads) :
    markedMemoryCopiedSlotEmbedding src σ k = src (σ k.castSucc) := rfl

theorem markedMemoryCopiedSlotEmbedding_batch {A : Type*} [DecidableEq A] {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (σ : Equiv.Perm (Fin (pads+1))) (out : Fin (pads+1))
    (hσ : σ (Fin.last pads) = out) :
    markedMemoryBirthBatch (markedMemoryCopiedSlotEmbedding src σ) =
      (markedMemoryBirthBatch src).erase (src out) := by
  classical
  ext x
  simp only [markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_erase,
    markedMemoryCopiedSlotEmbedding_apply]
  constructor
  · rintro ⟨k,rfl⟩
    refine ⟨?_, σ k.castSucc, rfl⟩
    intro he
    exact Fin.castSucc_ne_last k (σ.injective ((src.injective he).trans hσ.symm))
  · rintro ⟨hx,i,hi⟩
    have hio : i ≠ out := by
      intro he
      exact hx (hi.symm.trans (congrArg src he))
    have hpre : σ.symm i ≠ Fin.last pads := by
      intro he
      have hh := congrArg σ he
      exact hio (by simpa only [Equiv.apply_symm_apply, hσ] using hh)
    obtain ⟨k,hk⟩ := Fin.exists_castSucc_eq.mpr hpre
    refine ⟨k,?_⟩
    simpa only [hk, Equiv.apply_symm_apply] using hi

def markedMemoryRemainingSlotEmbedding {A : Type*} {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (out : Fin (pads+1)) : Fin pads ↪ A :=
  markedMemoryCopiedSlotEmbedding src (Equiv.swap (Fin.last pads) out)

@[simp] theorem markedMemoryRemainingSlotEmbedding_apply {A : Type*} {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (out : Fin (pads+1)) (k : Fin pads) :
    markedMemoryRemainingSlotEmbedding src out k = src (Equiv.swap (Fin.last pads) out k.castSucc) := rfl

theorem markedMemoryRemainingSlotEmbedding_batch {A : Type*} [DecidableEq A] {pads : ℕ}
    (src : Fin (pads+1) ↪ A) (out : Fin (pads+1)) :
    markedMemoryBirthBatch (markedMemoryRemainingSlotEmbedding src out) =
      (markedMemoryBirthBatch src).erase (src out) :=
  markedMemoryCopiedSlotEmbedding_batch src _ out (Equiv.swap_apply_left _ _)

variable {A : Type*} [DecidableEq A] {pads : ℕ}
  (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
  (hremaining : (markedMemoryBirthBatch src).erase (src out) =
    (markedMemoryBirthBatch dst).erase (dst inc))

include hremaining

theorem markedMemoryRemainingSlotMatching_exists :
    ∃! μ : Equiv.Perm (Fin pads),
      markedMemoryBirthReindex (markedMemoryRemainingSlotEmbedding dst inc) μ =
        markedMemoryRemainingSlotEmbedding src out := by
  apply (markedMemoryBirth_eq_iff_reindex _ _).mp
  rw [markedMemoryRemainingSlotEmbedding_batch, markedMemoryRemainingSlotEmbedding_batch]
  exact hremaining.symm

def markedMemoryRemainingSlotMatching : Equiv.Perm (Fin pads) :=
  Classical.choose (markedMemoryRemainingSlotMatching_exists src dst out inc hremaining)

theorem markedMemoryRemainingSlotMatching_apply (k : Fin pads) :
    dst (Equiv.swap (Fin.last pads) inc (markedMemoryRemainingSlotMatching src dst out inc hremaining k).castSucc) =
      src (Equiv.swap (Fin.last pads) out k.castSucc) :=
  congrArg (fun e : Fin pads ↪ A => e k)
    (Classical.choose_spec (markedMemoryRemainingSlotMatching_exists src dst out inc hremaining)).1

theorem markedMemoryRemainingSlotMatching_unique (μ : Equiv.Perm (Fin pads))
    (hμ : ∀ k, dst (Equiv.swap (Fin.last pads) inc (μ k).castSucc) =
      src (Equiv.swap (Fin.last pads) out k.castSucc)) :
    μ = markedMemoryRemainingSlotMatching src dst out inc hremaining := by
  apply Equiv.ext
  intro k
  apply (markedMemoryRemainingSlotEmbedding dst inc).injective
  exact (hμ k).trans (markedMemoryRemainingSlotMatching_apply src dst out inc hremaining k).symm

end
end ArtinMatthews
