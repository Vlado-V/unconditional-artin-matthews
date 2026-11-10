module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Basify
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.ENatToNat
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

/-! Distinct birth identities, rather than distinct numeric marks, have free indexed permutation
orbits. The exact fiber cardinality cancels the literal birth factorial. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

/-- The unordered set of genuinely distinct birth identities in an ordered injection. -/
def markedMemoryBirthBatch {X : Type*} {n : ℕ} (e : Fin n ↪ X) : Finset X :=
  Finset.univ.map e

theorem markedMemoryBirthBatch_card {X : Type*} {n : ℕ} (e : Fin n ↪ X) :
    (markedMemoryBirthBatch e).card = n := by simp [markedMemoryBirthBatch]

/-- Actual index reindexing; it is free even when numeric marks of identities coincide. -/
def markedMemoryBirthReindex {X : Type*} {n : ℕ}
    (e : Fin n ↪ X) (π : Equiv.Perm (Fin n)) : Fin n ↪ X :=
  π.toEmbedding.trans e

@[simp] theorem markedMemoryBirthReindex_apply {X : Type*} {n : ℕ}
    (e : Fin n ↪ X) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    markedMemoryBirthReindex e π i = e (π i) := rfl

theorem markedMemoryBirthReindex_injective {X : Type*} {n : ℕ} (e : Fin n ↪ X) :
    Function.Injective (markedMemoryBirthReindex e) := by
  intro π τ h
  apply Equiv.ext
  intro i
  apply e.injective
  exact congrArg (fun f : Fin n ↪ X => f i) h

theorem markedMemoryBirthBatch_reindex {X : Type*} {n : ℕ}
    (e : Fin n ↪ X) (π : Equiv.Perm (Fin n)) :
    markedMemoryBirthBatch (markedMemoryBirthReindex e π) = markedMemoryBirthBatch e := by
  classical
  ext x
  simp only [markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and,
    markedMemoryBirthReindex_apply]
  exact ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩,
    fun ⟨i, hi⟩ => ⟨π.symm i, by simpa using hi⟩⟩

/-- Cardinal-n identity sets, with no condition on any subsequently attached numeric mark. -/
abbrev MarkedMemoryBirthSets (X : Type*) (n : ℕ) := {S : Finset X // S.card = n}

def markedMemoryBirthSet {X : Type*} {n : ℕ} (e : Fin n ↪ X) :
    MarkedMemoryBirthSets X n := ⟨markedMemoryBirthBatch e, markedMemoryBirthBatch_card e⟩

/-- Enumerating a fixed birth set is exactly giving a bijection from its indexed birth slots. -/
def markedMemoryBirthFiberEquiv {X : Type*} {n : ℕ} (S : MarkedMemoryBirthSets X n) :
    {e : Fin n ↪ X // markedMemoryBirthSet e = S} ≃ (Fin n ≃ ↥S.1) := by
  classical
  refine
    { toFun := fun e => Equiv.ofBijective
        (fun i => ⟨e.1 i, ?_⟩) ⟨?_, ?_⟩
      invFun := fun f => ⟨f.toEmbedding.trans (Function.Embedding.subtype (· ∈ S.1)), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have he := congrArg Subtype.val e.2
    change markedMemoryBirthBatch e.1 = S.1 at he
    rw [← he]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro i j hij
    exact e.1.injective (congrArg Subtype.val hij)
  · intro x
    have he := congrArg Subtype.val e.2
    change markedMemoryBirthBatch e.1 = S.1 at he
    have hx : x.1 ∈ markedMemoryBirthBatch e.1 := by simpa only [he] using x.2
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
    exact ⟨i, Subtype.ext hi⟩
  · apply Subtype.ext
    ext x
    simp only [markedMemoryBirthSet, markedMemoryBirthBatch, Finset.mem_map,
      Finset.mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact (f i).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)⟩
  · intro e
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  · intro f
    apply Equiv.ext
    intro i
    rfl

/-- The exact enumeration fiber has n! elements, including for n=0. -/
theorem markedMemoryBirthFiber_card {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (S : MarkedMemoryBirthSets X n) :
    Fintype.card {e : Fin n ↪ X // markedMemoryBirthSet e = S} = n.factorial := by
  classical
  rw [Fintype.card_congr (markedMemoryBirthFiberEquiv S),
    Fintype.card_equiv (Finset.equivFinOfCardEq S.2).symm, Fintype.card_fin]

/-- Equal unordered identity batches differ by a unique actual index permutation. -/
theorem markedMemoryBirth_eq_iff_reindex {X : Type*} {n : ℕ} (e f : Fin n ↪ X) :
    markedMemoryBirthBatch e = markedMemoryBirthBatch f ↔
      ∃! π : Equiv.Perm (Fin n), markedMemoryBirthReindex e π = f := by
  classical
  constructor
  · intro h
    let S := markedMemoryBirthSet e
    let ee := markedMemoryBirthFiberEquiv S ⟨e, rfl⟩
    let ff := markedMemoryBirthFiberEquiv S ⟨f, Subtype.ext h.symm⟩
    refine ⟨ff.trans ee.symm, ?_, ?_⟩
    · apply Function.Embedding.ext
      intro i
      have he := congrArg Subtype.val (ee.apply_symm_apply (ff i))
      exact he
    · intro π hπ
      apply markedMemoryBirthReindex_injective e
      exact hπ.trans (by
        apply Function.Embedding.ext
        intro i
        exact (congrArg Subtype.val (ee.apply_symm_apply (ff i))).symm)
  · rintro ⟨π, hπ, _⟩
    rw [← hπ, markedMemoryBirthBatch_reindex]

/-- Exact n! cancellation after summing all orderings of distinct identity batches. -/
theorem markedMemoryBirth_normalized_sum {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (F : MarkedMemoryBirthSets X n → ℂ) :
    (∑ e : Fin n ↪ X, F (markedMemoryBirthSet e) / (n.factorial : ℂ)) = ∑ S, F S := by
  classical
  rw [← Fintype.sum_fiberwise (markedMemoryBirthSet (X := X) (n := n))]
  apply Finset.sum_congr rfl
  intro S _
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [show ∀ e : {e : Fin n ↪ X // markedMemoryBirthSet e = S},
    F (markedMemoryBirthSet e.1) / (n.factorial : ℂ) = F S / (n.factorial : ℂ)
      from fun e => by rw [e.2]]
  rw [Finset.sum_const, Finset.card_univ, markedMemoryBirthFiber_card, nsmul_eq_mul]
  field_simp

/-- One chosen enumeration of an identity set; no ordering of its numeric marks is used. -/
def markedMemoryBirthCanonical {X : Type*} {n : ℕ} (S : MarkedMemoryBirthSets X n) :
    Fin n ↪ X :=
  ((markedMemoryBirthFiberEquiv S).symm (Finset.equivFinOfCardEq S.2).symm).1

theorem markedMemoryBirthCanonical_set {X : Type*} {n : ℕ} (S : MarkedMemoryBirthSets X n) :
    markedMemoryBirthSet (markedMemoryBirthCanonical S) = S :=
  ((markedMemoryBirthFiberEquiv S).symm (Finset.equivFinOfCardEq S.2).symm).2

/-- Arbitrary permutation-invariant history weights descend exactly to unordered identity sets. -/
theorem markedMemoryBirth_normalized_symmetric_sum {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} (W : (Fin n ↪ X) → ℂ)
    (hW : ∀ e π, W (markedMemoryBirthReindex e π) = W e) :
    (∑ e : Fin n ↪ X, W e / (n.factorial : ℂ)) =
      ∑ S : MarkedMemoryBirthSets X n, W (markedMemoryBirthCanonical S) := by
  classical
  have heq (e : Fin n ↪ X) : W e = W (markedMemoryBirthCanonical (markedMemoryBirthSet e)) := by
    have hb : markedMemoryBirthBatch (markedMemoryBirthCanonical (markedMemoryBirthSet e)) =
        markedMemoryBirthBatch e :=
      congrArg Subtype.val (markedMemoryBirthCanonical_set (markedMemoryBirthSet e))
    obtain ⟨π, hπ, _⟩ := (markedMemoryBirth_eq_iff_reindex _ _).mp hb
    exact (congrArg W hπ).symm.trans (hW _ π)
  calc
    _ = ∑ e : Fin n ↪ X,
        W (markedMemoryBirthCanonical (markedMemoryBirthSet e)) / (n.factorial : ℂ) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [heq e]
    _ = _ := markedMemoryBirth_normalized_sum (fun S => W (markedMemoryBirthCanonical S))

/-- Product weights descend by identity, with arbitrary possibly repeated numeric marks. -/
theorem markedMemoryBirth_product {X A : Type*} {n : ℕ}
    (mark : X → A) (weight : A → ℂ) (e : Fin n ↪ X) :
    (∏ i, weight (mark (e i))) = ∏ x ∈ markedMemoryBirthBatch e, weight (mark x) := by
  classical
  simp [markedMemoryBirthBatch]

/-- The normalized marked-batch sum preserves repeated numeric values on distinct identities. -/
theorem markedMemoryBirth_normalized_product_sum {X A : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (mark : X → A) (weight : A → ℂ) :
    (∑ e : Fin n ↪ X, (∏ i, weight (mark (e i))) / (n.factorial : ℂ)) =
      ∑ S : MarkedMemoryBirthSets X n, ∏ x ∈ S.1, weight (mark x) := by
  classical
  simpa only [markedMemoryBirth_product, markedMemoryBirthSet] using
    markedMemoryBirth_normalized_sum (n := n)
      (fun S : MarkedMemoryBirthSets X n => ∏ x ∈ S.1, weight (mark x))

end
end ArtinMatthews
