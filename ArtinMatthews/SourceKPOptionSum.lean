module

public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem sourceKPOptionSum {α : Type*} (f : Option α → ℂ) (hf : Summable f) :
    (∑' t, f t) = f none + ∑' x : α, f (some x) := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit α
  have he : Summable (fun t => f (e.symm t)) := e.symm.summable_iff.mpr hf
  rw [← e.symm.tsum_eq, (he.comp_injective Sum.inl_injective).tsum_sum
    (he.comp_injective Sum.inr_injective)]
  simp only [e, Equiv.optionEquivSumPUnit_symm_inl,
    Equiv.optionEquivSumPUnit_symm_inr, tsum_fintype, Fintype.sum_unique]
  exact add_comm _ _

end
end ArtinMatthews
