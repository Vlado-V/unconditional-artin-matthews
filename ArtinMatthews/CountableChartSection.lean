module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Data.Countable.Defs


set_option backward.privateInPublic true
@[expose] public section

/-! Selecting the first chart in a countable measurable cover gives a
measurable exact set of representatives. -/
namespace ArtinMatthews
open Set

theorem exists_measurable_chart_section
    {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
    (p : X → Y) (hp : Measurable p) (U : I → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hm : ∀ i, MeasurableSet (p '' U i))
    (hi : ∀ i, Set.InjOn p (U i))
    (hc : ∀ y, ∃ i, y ∈ p '' U i) :
    ∃ F : Set X, MeasurableSet F ∧ F ⊆ ⋃ i, U i ∧ Set.InjOn p F ∧ p '' F = Set.univ := by
  classical
  let : Encodable I := Encodable.ofCountable I
  let Earlier (i : I) := {j : I // Encodable.encode j < Encodable.encode i}
  let V (i : I) := U i \ p ⁻¹' (⋃ j : Earlier i, p '' U j.val)
  let F := ⋃ i, V i
  refine ⟨F, ?_, ?_, ?_, Set.eq_univ_of_forall ?_⟩
  · exact MeasurableSet.iUnion fun i =>
      (hU i).diff ((MeasurableSet.iUnion fun j : Earlier i => hm j.val).preimage hp)
  · intro x hx
    obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i,hxi.1⟩
  · intro x hx y hy hxy
    obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j,hyj⟩ := Set.mem_iUnion.mp hy
    rcases lt_trichotomy (Encodable.encode i) (Encodable.encode j) with hij | hij | hji
    · exact False.elim (hyj.2 (Set.mem_iUnion.mpr ⟨⟨i,hij⟩,x,hxi.1,hxy⟩))
    · have h := Encodable.encode_injective hij
      subst j
      exact hi i hxi.1 hyj.1 hxy
    · exact False.elim (hxi.2 (Set.mem_iUnion.mpr ⟨⟨j,hji⟩,y,hyj.1,hxy.symm⟩))
  · intro y
    let P (n : ℕ) := ∃ i : I, Encodable.encode i = n ∧ y ∈ p '' U i
    have hP : ∃ n, P n := by
      obtain ⟨i,hi'⟩ := hc y
      exact ⟨Encodable.encode i,i,rfl,hi'⟩
    obtain ⟨i,hei,x,hx,hpx⟩ := Nat.find_spec hP
    refine ⟨x,Set.mem_iUnion.mpr ⟨i,hx,?_⟩,hpx⟩
    intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hlt : Encodable.encode j.val < Nat.find hP := hei ▸ j.property
    apply Nat.find_min hP hlt
    exact ⟨j.val,rfl,hpx ▸ hj⟩

end ArtinMatthews
