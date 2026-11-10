module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
public import ArtinMatthews.MarkedMinorArcRawState
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite degree coordinates for the literal edge choices.  Both
total cutoffs are retained, and the zero-or-one deletion batch still
records the selected old index, including repeated particle values. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def markedRawEdgeBit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem markedRawEdgeBit_false : markedRawEdgeBit false = 0 := rfl
@[simp] theorem markedRawEdgeBit_true : markedRawEdgeBit true = 1 := rfl

theorem markedRawEdgeBit_injective : Function.Injective markedRawEdgeBit := by
  intro a b h
  cases a <;> cases b <;> simp_all

theorem markedRawEdgeBit_le_one (b : Bool) : markedRawEdgeBit b ≤ 1 := by
  cases b <;> decide

@[ext] structure MarkedRawEdgeDegrees (J : Type*) [Fintype J] (B : ℕ) where
  survivors : J → ℕ
  promoted : J → Bool
  stored : J → Bool
  source_le : ∑ j, (survivors j+markedRawEdgeBit (promoted j)) ≤ B
  target_le : ∑ j, (survivors j+markedRawEdgeBit (stored j)) ≤ B

def markedRawEdgeDegreesSwap {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawEdgeDegrees J B ≃ MarkedRawEdgeDegrees J B where
  toFun t := ⟨t.survivors,t.stored,t.promoted,t.target_le,t.source_le⟩
  invFun t := ⟨t.survivors,t.stored,t.promoted,t.target_le,t.source_le⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedRawEdgeDegrees_source_le {J : Type*} [Fintype J] {B : ℕ}
    (t : MarkedRawEdgeDegrees J B) (j : J) :
    t.survivors j+markedRawEdgeBit (t.promoted j) ≤ B :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le
    (t.survivors i+markedRawEdgeBit (t.promoted i))) (Finset.mem_univ j)).trans t.source_le

theorem markedRawEdgeDegrees_target_le {J : Type*} [Fintype J] {B : ℕ}
    (t : MarkedRawEdgeDegrees J B) (j : J) :
    t.survivors j+markedRawEdgeBit (t.stored j) ≤ B :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le
    (t.survivors i+markedRawEdgeBit (t.stored i))) (Finset.mem_univ j)).trans t.target_le

def markedRawEdgeDegreesEmbedding {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawEdgeDegrees J B ↪ ((J → Fin (B+1)) × (J → Bool) × (J → Bool)) where
  toFun t := (fun j => ⟨t.survivors j,by have := markedRawEdgeDegrees_source_le t j; omega⟩,
    t.promoted,t.stored)
  inj' := by
    intro a b h
    apply MarkedRawEdgeDegrees.ext
    · funext j
      exact congrArg (fun v => (v.1 j:ℕ)) h
    · exact congrArg (fun v => v.2.1) h
    · exact congrArg (fun v => v.2.2) h

instance {J : Type*} [Fintype J] {B : ℕ} : Finite (MarkedRawEdgeDegrees J B) :=
  Finite.of_injective markedRawEdgeDegreesEmbedding markedRawEdgeDegreesEmbedding.injective

instance {J : Type*} [Fintype J] {B : ℕ} : Fintype (MarkedRawEdgeDegrees J B) := Fintype.ofFinite _

def markedRawEdgeDegreesSourceSizes {J : Type*} [Fintype J] {B : ℕ}
    (t : MarkedRawEdgeDegrees J B) : MarkedRawMemorySizes J B :=
  ⟨fun j => ⟨t.survivors j+markedRawEdgeBit (t.promoted j),by
    have := markedRawEdgeDegrees_source_le t j; omega⟩,t.source_le⟩

theorem markedRawEdgeOption_card {k : ℕ} (p : Option (Fin k)) :
    p.toFinset.card=markedRawEdgeBit p.isSome := by
  cases p <;> rfl

theorem markedRawEdgeOption_injective {k : ℕ} :
    Function.Injective (fun p : Option (Fin k) => p.toFinset) := by
  intro p q h
  cases p <;> cases q <;> simp_all

theorem markedRawEdgeBatchOption_exists {k : ℕ} {b : Bool}
    (S : MarkedRawDeletionBatch k (markedRawEdgeBit b)) :
    ∃ p : Option (Fin k), p.toFinset=S.1 ∧ p.isSome=b := by
  have hS := markedRawDeletionBatch_deleted_card S
  cases b with
  | false =>
    refine ⟨none,?_,rfl⟩
    exact (Finset.card_eq_zero.mp hS).symm
  | true =>
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hS
    exact ⟨some i,hi.symm,rfl⟩

def markedRawEdgeBatchOption {k : ℕ} {b : Bool}
    (S : MarkedRawDeletionBatch k (markedRawEdgeBit b)) : Option (Fin k) :=
  (markedRawEdgeBatchOption_exists S).choose

theorem markedRawEdgeBatchOption_toFinset {k : ℕ} {b : Bool}
    (S : MarkedRawDeletionBatch k (markedRawEdgeBit b)) :
    (markedRawEdgeBatchOption S).toFinset=S.1 :=
  (markedRawEdgeBatchOption_exists S).choose_spec.1

theorem markedRawEdgeBatchOption_isSome {k : ℕ} {b : Bool}
    (S : MarkedRawDeletionBatch k (markedRawEdgeBit b)) :
    (markedRawEdgeBatchOption S).isSome=b :=
  (markedRawEdgeBatchOption_exists S).choose_spec.2

abbrev MarkedRawEdgeShape (J : Type*) [Fintype J] (B : ℕ) :=
  Σ k : MarkedRawMemorySizes J B,
    Σ p : (j : J) → Option (Fin (k.1 j:ℕ)),
      {stored : J → Bool //
        ∑ j, ((Finset.univ \ (p j).toFinset).card+markedRawEdgeBit (stored j)) ≤ B}

abbrev MarkedRawEdgeDegreeShape (J : Type*) [Fintype J] (B : ℕ) :=
  Σ t : MarkedRawEdgeDegrees J B,
    (j : J) → MarkedRawDeletionBatch
      (t.survivors j+markedRawEdgeBit (t.promoted j)) (markedRawEdgeBit (t.promoted j))

def markedRawEdgeDegreeShapeToShape {J : Type*} [Fintype J] {B : ℕ}
    (a : MarkedRawEdgeDegreeShape J B) : MarkedRawEdgeShape J B :=
  ⟨markedRawEdgeDegreesSourceSizes a.1,fun j => markedRawEdgeBatchOption (a.2 j),
    ⟨a.1.stored,by
      have hn (j : J) : (Finset.univ \ (markedRawEdgeBatchOption (a.2 j)).toFinset).card=
          a.1.survivors j := by
        rw [markedRawEdgeBatchOption_toFinset,← Finset.compl_eq_univ_sdiff]
        exact markedRawDeletionBatch_survivor_card rfl (a.2 j)
      calc
        _ = ∑ j, (a.1.survivors j+markedRawEdgeBit (a.1.stored j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hn j]
        _ ≤ B := a.1.target_le⟩⟩

theorem markedRawEdgeDegreeShapeToShape_injective {J : Type*} [Fintype J] {B : ℕ} :
    Function.Injective (markedRawEdgeDegreeShapeToShape (J := J) (B := B)) := by
  intro a b hab
  have ht : a.1=b.1 := by
    apply MarkedRawEdgeDegrees.ext
    · funext j
      have hh := congrArg
        (fun v : MarkedRawEdgeShape J B => (Finset.univ \ (v.2.1 j).toFinset).card) hab
      change (Finset.univ \ (markedRawEdgeBatchOption (a.2 j)).toFinset).card=
        (Finset.univ \ (markedRawEdgeBatchOption (b.2 j)).toFinset).card at hh
      rw [markedRawEdgeBatchOption_toFinset,markedRawEdgeBatchOption_toFinset,
        ← Finset.compl_eq_univ_sdiff,← Finset.compl_eq_univ_sdiff,
        markedRawDeletionBatch_survivor_card rfl,markedRawDeletionBatch_survivor_card rfl] at hh
      exact hh
    · funext j
      have hh := congrArg (fun v : MarkedRawEdgeShape J B => (v.2.1 j).isSome) hab
      exact (markedRawEdgeBatchOption_isSome (a.2 j)).symm.trans
        (hh.trans (markedRawEdgeBatchOption_isSome (b.2 j)))
    · exact congrArg (fun v : MarkedRawEdgeShape J B => v.2.2.1) hab
  rcases a with ⟨t,S⟩
  rcases b with ⟨t',S'⟩
  dsimp only at ht
  cases ht
  have htail := eq_of_heq (Sigma.mk.inj_iff.mp hab).2
  have hprom := congrArg Sigma.fst htail
  have hS : S=S' := by
    funext j
    apply Subtype.ext
    exact (markedRawEdgeBatchOption_toFinset (S j)).symm.trans
      ((congrArg Option.toFinset (congrFun hprom j)).trans
        (markedRawEdgeBatchOption_toFinset (S' j)))
  cases hS
  rfl

theorem markedRawEdgeDegreeShapeToShape_surjective {J : Type*} [Fintype J] {B : ℕ} :
    Function.Surjective (markedRawEdgeDegreeShapeToShape (J := J) (B := B)) := by
  rintro ⟨k,p,stored⟩
  let t : MarkedRawEdgeDegrees J B :=
    ⟨fun j => (Finset.univ \ (p j).toFinset).card,fun j => (p j).isSome,stored.1,by
      have hh (j : J) : (Finset.univ \ (p j).toFinset).card+
          markedRawEdgeBit (p j).isSome=(k.1 j:ℕ) := by
        rw [← markedRawEdgeOption_card]
        simpa only [Finset.card_univ,Fintype.card_fin] using
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (p j).toFinset)
      simpa only [hh] using k.2,stored.2⟩
  have hn (j : J) : (Finset.univ \ (p j).toFinset).card=t.survivors j := rfl
  have hp (j : J) : (p j).isSome=t.promoted j := rfl
  have hs : stored.1=t.stored := rfl
  clear_value t
  have hk : markedRawEdgeDegreesSourceSizes t=k := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (p j).toFinset)
    simpa only [markedRawEdgeDegreesSourceSizes,Finset.card_univ,Fintype.card_fin,
      markedRawEdgeOption_card,hn,hp] using hh
  cases hk
  let S : (j : J) → MarkedRawDeletionBatch
      (t.survivors j+markedRawEdgeBit (t.promoted j)) (markedRawEdgeBit (t.promoted j)) :=
    fun j => ⟨(p j).toFinset,Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,(markedRawEdgeOption_card (p j)).trans (congrArg markedRawEdgeBit (hp j))⟩⟩
  have hS : (fun j => markedRawEdgeBatchOption (S j))=p := by
    funext j
    apply markedRawEdgeOption_injective
    exact markedRawEdgeBatchOption_toFinset (S j)
  clear_value S
  refine ⟨⟨t,S⟩,?_⟩
  apply congrArg (fun tail => (⟨markedRawEdgeDegreesSourceSizes t,tail⟩ : MarkedRawEdgeShape J B))
  dsimp only [markedRawEdgeDegreeShapeToShape]
  cases hS
  apply congrArg (fun tail => (⟨(fun j => markedRawEdgeBatchOption (S j)),tail⟩ :
    Σ p : (j : J) → Option (Fin ((markedRawEdgeDegreesSourceSizes t).1 j:ℕ)),
      {stored : J → Bool // ∑ j, ((Finset.univ \ (p j).toFinset).card+
        markedRawEdgeBit (stored j)) ≤ B}))
  exact Subtype.ext hs.symm

def markedRawEdgeDegreeShapeEquiv {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawEdgeDegreeShape J B ≃ MarkedRawEdgeShape J B :=
  Equiv.ofBijective markedRawEdgeDegreeShapeToShape
    ⟨markedRawEdgeDegreeShapeToShape_injective,markedRawEdgeDegreeShapeToShape_surjective⟩

end
end ArtinMatthews
