module

public import ArtinMatthews.MarkedMemoryQueueRelabel
public import ArtinMatthews.MarkedMemoryIndependentLifespans
public import ArtinMatthews.MarkedMemoryQueueState
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Genuine per-band relabeling of independent tableaux. Physical
particles and positions are unchanged; only identity names are moved
along the supplied equivalences. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentRelabel :
    MarkedMemoryIndependentLifespans (A := A') (P := P) (pads := pads) (B := B) hZ n where
  lifespan j := markedMemoryQueueRelabel (e j) (d.lifespan j)
  position := d.position
  activeId v j := (d.activeId v j).trans (e j).toEmbedding
  particle j a := d.particle j ((e j).symm a)
  active_mem := by
    intro v hv j a
    change (d.lifespan j).active (2*v) ((e j).symm a) ↔ ∃ i, e j (d.activeId v j i) = a
    rw [d.active_mem v hv j]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i,(e j).eq_symm_apply.mp hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,(e j).eq_symm_apply.mpr hi⟩
  active_alive := by
    intro v hv j i
    simpa only [markedMemoryQueueRelabel, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply] using d.active_alive v hv j i
  cutoff := by
    intro t ht
    calc
      _ = ∑ j, (markedMemoryPendingIdentitySet (d.lifespan j) t).card := by
        apply Finset.sum_congr rfl
        intro j _
        exact markedMemoryQueueRelabel_pending_card (e j) (d.lifespan j) t ht
      _ ≤ B := d.cutoff t ht
  ghost_death_hit := by
    intro v hv j a hf hl hn
    exact d.ghost_death_hit v hv j ((e j).symm a) hf hl hn
  ghost_birth_anchor := by
    intro v hv j a hb
    exact d.ghost_birth_anchor v hv j ((e j).symm a)
      ((markedMemoryRelabel_mem_map (e j) ((d.lifespan j).births (2*v)) a).mp hb)
  promotion_hit := by
    intro v hv j hf hl hn
    simpa only [markedMemoryQueueRelabel, Equiv.symm_apply_apply] using d.promotion_hit v hv j
      (by simpa only [markedMemoryQueueRelabel, Equiv.symm_apply_apply] using hf)
      (by simpa only [markedMemoryQueueRelabel, Equiv.symm_apply_apply] using hl)
      (by simpa only [markedMemoryQueueRelabel, Equiv.symm_apply_apply] using hn)
  store_anchor := by
    intro v hv j hl
    simpa only [markedMemoryQueueRelabel, Equiv.symm_apply_apply] using d.store_anchor v hv j
      (by simpa only [markedMemoryQueueRelabel, Equiv.symm_apply_apply] using hl)

theorem markedMemoryIndependentRelabel_queue (t : ℕ) (j : J) :
    markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) t j =
      (markedMemoryIndependentQueue hZ d t j).map (e j) :=
  markedMemoryQueueRelabel_queue (e j) (d.lifespan j) t

theorem markedMemoryIndependentRelabel_memory (t : ℕ) (ht : t ≤ 2*n+1) :
    markedMemoryIndependentMemory hZ (markedMemoryIndependentRelabel hZ e d) t ht =
      markedMemoryIndependentMemory hZ d t ht := by
  apply markedMemoryState_eq_of_lists
  intro j
  simp only [markedMemoryIndependentMemory, markedMemoryLabeledQueueState_list]
  change (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) t j).map
    (fun a => d.particle j ((e j).symm a)) = (markedMemoryIndependentQueue hZ d t j).map (d.particle j)
  rw [markedMemoryIndependentRelabel_queue, List.map_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

theorem markedMemoryIndependentRelabel_state (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentState hZ (markedMemoryIndependentRelabel hZ e d) v hv =
      markedMemoryIndependentState hZ d v hv := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext j k
    change (d.particle j ((e j).symm (e j (d.activeId v j k)))).1 = (d.particle j (d.activeId v j k)).1
    rw [Equiv.symm_apply_apply]
  · exact markedMemoryIndependentRelabel_memory hZ e d (2*v) (by omega)

theorem markedMemoryIndependentRelabel_postGhost (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentPostGhost hZ (markedMemoryIndependentRelabel hZ e d) v hv =
      markedMemoryIndependentPostGhost hZ d v hv := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext j k
    change (d.particle j ((e j).symm (e j (d.activeId v j k)))).1 = (d.particle j (d.activeId v j k)).1
    rw [Equiv.symm_apply_apply]
  · exact markedMemoryIndependentRelabel_memory hZ e d (2*v+1) (by omega)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentLifespans_ext
    (f : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (hl : d.lifespan = f.lifespan) (hp : d.position = f.position)
    (ha : d.activeId = f.activeId) (hpart : d.particle = f.particle) : d = f := by
  cases d
  cases f
  cases hl
  cases hp
  cases ha
  cases hpart
  rfl

theorem markedMemoryIndependentRelabel_symm :
    markedMemoryIndependentRelabel hZ (fun j => (e j).symm) (markedMemoryIndependentRelabel hZ e d) = d := by
  apply markedMemoryIndependentLifespans_ext
  · funext j
    exact markedMemoryQueueRelabel_symm (e j) (d.lifespan j)
  · rfl
  · funext v j
    apply Function.Embedding.ext
    intro k
    exact (e j).symm_apply_apply (d.activeId v j k)
  · funext j a
    exact congrArg (d.particle j) ((e j).symm_apply_apply a)

def markedMemoryIndependentRelabelEquiv :
    MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n ≃
      MarkedMemoryIndependentLifespans (A := A') (P := P) (pads := pads) (B := B) hZ n where
  toFun := markedMemoryIndependentRelabel hZ e
  invFun := markedMemoryIndependentRelabel hZ (fun j => (e j).symm)
  left_inv := markedMemoryIndependentRelabel_symm hZ e
  right_inv f := by
    simpa only [Equiv.symm_symm] using markedMemoryIndependentRelabel_symm hZ (fun j => (e j).symm) f

def markedMemoryIndependentRelabelFin :
    MarkedMemoryIndependentLifespans (A := fun j => Fin (Fintype.card (A j)))
      (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryIndependentRelabel hZ (fun j => Fintype.equivFin (A j)) d

end
end ArtinMatthews
