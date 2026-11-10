module

public import Mathlib.Data.Finset.Sort
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

/-! Increasing finite-index retention is ordinary list filtering after
any label map, without injectivity of the labels. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryOfFn_filter {A : Type*} {N : ℕ} (f : Fin N → A)
    (keep : Finset (Fin N)) (p : A → Prop) [DecidablePred p]
    (hkeep : ∀ i, i ∈ keep ↔ p (f i)) :
    List.ofFn (fun k => f (keep.orderEmbOfFin rfl k)) =
      (List.ofFn f).filter (fun a => decide (p a)) := by
  classical
  let all : List (Fin N) := List.ofFn id
  let selected : List (Fin N) := List.ofFn (fun k => keep.orderEmbOfFin rfl k)
  let filtered := all.filter (fun i => decide (i ∈ keep))
  have hs : selected.toFinset = keep := by
    ext i
    simp only [selected,List.mem_toFinset,List.mem_ofFn]
    constructor
    · rintro ⟨k,rfl⟩
      exact (keep.orderIsoOfFin rfl k).2
    · intro hi
      exact ⟨(keep.orderIsoOfFin rfl).symm ⟨i,hi⟩,
        congrArg Subtype.val ((keep.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)⟩
  have hf : filtered.toFinset = keep := by
    ext i
    simp only [filtered,all,List.mem_toFinset,List.mem_filter,List.mem_ofFn,id_eq,
      exists_eq,decide_eq_true_eq,true_and]
  have hsn : selected.Nodup := List.nodup_ofFn_ofInjective (keep.orderEmbOfFin rfl).injective
  have hfn : filtered.Nodup := (List.nodup_ofFn_ofInjective Function.injective_id).filter _
  have hso : selected.Pairwise (· ≤ ·) := (keep.orderEmbOfFin rfl).monotone.sortedLE_ofFn.pairwise
  have hfo : filtered.Pairwise (· ≤ ·) := (monotone_id.sortedLE_ofFn : all.SortedLE).pairwise.filter _
  have hseq : keep.sort = selected := by
    simpa only [hs] using (List.toFinset_sort (r := (· ≤ ·)) hsn).mpr hso
  have hfeq : keep.sort = filtered := by
    simpa only [hf] using (List.toFinset_sort (r := (· ≤ ·)) hfn).mpr hfo
  calc
    _ = selected.map f := List.map_ofFn.symm
    _ = filtered.map f := congrArg (List.map f) (hseq.symm.trans hfeq)
    _ = (all.map f).filter (fun a => decide (p a)) := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro i _
      simpa only [Function.comp_apply,decide_eq_decide] using hkeep i
    _ = _ := by simp only [all,List.map_ofFn,Function.comp_id]

end
end ArtinMatthews
