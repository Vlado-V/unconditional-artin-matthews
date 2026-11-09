module

public import ArtinMatthews.MarkedMemoryQueueOrder


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
