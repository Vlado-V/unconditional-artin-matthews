module

public import Mathlib.MeasureTheory.Measure.Restrict


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set

theorem measure_eq_of_locally_restrict {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] (μ ν : Measure X)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ.restrict U = ν.restrict U) :
    μ = ν := by
  choose U hU hx hμ using h
  obtain ⟨S,hS,hcover⟩ := isLindelof_univ.elim_countable_subcover U hU (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hx x⟩)
  apply Measure.ext_of_biUnion_eq_univ hS (Set.eq_univ_of_univ_subset hcover)
  exact fun x _ => hμ x

end ArtinMatthews
