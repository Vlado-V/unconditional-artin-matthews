module

public import ArtinMatthews.MarkedMemoryIndexedQueues
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical increasing-index retention is exactly ordinary list
filtering, even when the stored numeric values repeat. This connects the
independent queue construction to the literal raw memory update order. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryRetainedQueue_filter_eq {A : Type*} (queue : List A)
    (p : A → Prop) [DecidablePred p] :
    markedMemoryRetainedQueue queue (Finset.univ.filter (fun i => p (queue.get i))) =
      queue.filter (fun a => decide (p a)) := by
  classical
  let keep : Finset (Fin queue.length) := Finset.univ.filter (fun i => p (queue.get i))
  let all : List (Fin queue.length) := List.ofFn id
  let selected : List (Fin queue.length) :=
    List.ofFn (fun i => (keep.orderIsoOfFin rfl i).1)
  let filtered := all.filter (fun i => decide (p (queue.get i)))
  have hs : selected.toFinset = keep := by
    ext i
    simp only [selected, List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨k,rfl⟩
      exact (keep.orderIsoOfFin rfl k).2
    · intro hi
      exact ⟨(keep.orderIsoOfFin rfl).symm ⟨i,hi⟩,
        congrArg Subtype.val ((keep.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)⟩
  have hf : filtered.toFinset = keep := by
    ext i
    simp only [filtered, all, keep, List.mem_toFinset, List.mem_filter,
      List.mem_ofFn, id_eq, exists_eq, decide_eq_true_eq, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hsn : selected.Nodup := by
    apply List.nodup_ofFn_ofInjective
    exact (keep.orderEmbOfFin rfl).injective
  have hfn : filtered.Nodup :=
    (List.nodup_ofFn_ofInjective (Function.injective_id)).filter _
  have hso : selected.Pairwise (· ≤ ·) :=
    (keep.orderEmbOfFin rfl).monotone.sortedLE_ofFn.pairwise
  have hfo : filtered.Pairwise (· ≤ ·) :=
    (monotone_id.sortedLE_ofFn : all.SortedLE).pairwise.filter _
  have hseq : keep.sort = selected := by
    have h := (List.toFinset_sort (r := (· ≤ ·)) hsn).mpr hso
    simpa only [hs] using h
  have hfeq : keep.sort = filtered := by
    have h := (List.toFinset_sort (r := (· ≤ ·)) hfn).mpr hfo
    simpa only [hf] using h
  have hindices : selected = filtered := hseq.symm.trans hfeq
  calc
    markedMemoryRetainedQueue queue keep = selected.map queue.get := by
      exact List.map_ofFn.symm
    _ = filtered.map queue.get := congrArg (List.map queue.get) hindices
    _ = (all.map queue.get).filter (fun a => decide (p a)) := by
      rw [List.filter_map]
      rfl
    _ = queue.filter (fun a => decide (p a)) := by
      simp only [all, List.map_ofFn, Function.comp_id, List.ofFn_get]

theorem markedMemoryIndexedGhostQueue_eq {A : Type*} (queue born : List A) (last : A → ℕ) (t : ℕ) :
    markedMemoryIndexedGhostQueue queue born last t = markedMemoryGhostQueue queue born last t := by
  unfold markedMemoryIndexedGhostQueue markedMemoryGhostQueue
  exact congrArg (fun l => l ++ born) (markedMemoryRetainedQueue_filter_eq queue (fun a => t < last a))

end
end ArtinMatthews
