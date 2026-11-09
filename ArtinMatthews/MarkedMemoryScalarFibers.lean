module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalar


set_option backward.privateInPublic true
@[expose] public section

/-! Finite scalar fibers and the exact contribution of a nodup family of
ordered identity lists. The indexing equivalences are constructed from
literal indices, independently of numerical prime labels. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {X Y M : Type*} [Fintype X] [DecidableEq Y] [CommMonoid M]

theorem markedMemoryScalarFiber_ite (label : X → Y) (a : Y) (value : X → M) :
    (∏ x : {x : X // label x = a}, value x.1) =
      ∏ x : X, if label x = a then value x else 1 := by
  symm
  apply Finset.prod_congr_set {x : X | label x = a}
  · intro x hx
    exact ite_eq_left hx
  · intro x hx
    exact ite_eq_right hx

theorem markedMemoryScalarFiber_single (label : X → Y) (hl : Function.Injective label)
    (a : Y) (value : X → M) (c : M) (hc : ∀ x, label x = a → value x = c) :
    (∏ x : X, if label x = a then value x else 1) =
      if (∃ x, label x = a) then c else 1 := by
  calc
    _ = ∏ x : X, if label x = a then c else 1 := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases h : label x = a
      · rw [ite_eq_left h, ite_eq_left h, hc x h]
      · rw [ite_eq_right h, ite_eq_right h]
    _ = _ := Fintype.prod_ite_eq_ite_exists (fun x => label x = a)
      (fun x y hx hy => hl (hx.trans hy.symm)) c

variable {J : Type*} [Fintype J] {A : J → Type*}

def markedMemoryListFamilyLabel (lists : (j : J) → List (A j)) :
    (Σ j, Fin (lists j).length) → Σ j, A j :=
  fun a => ⟨a.1,(lists a.1).get a.2⟩

omit [Fintype J] in
theorem markedMemoryListFamilyLabel_injective (lists : (j : J) → List (A j))
    (hn : ∀ j, (lists j).Nodup) : Function.Injective (markedMemoryListFamilyLabel lists) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ he
  change (⟨i,(lists i).get k⟩ : Σ j, A j) = ⟨j,(lists j).get l⟩ at he
  obtain ⟨rfl,hget⟩ := Sigma.mk.inj_iff.mp he
  exact congrArg (Sigma.mk i) ((List.nodup_iff_injective_get.mp (hn i)) (eq_of_heq hget))

omit [Fintype J] in
theorem markedMemoryListFamilyLabel_mem (lists : (j : J) → List (A j)) (a : Σ j, A j) :
    (∃ x, markedMemoryListFamilyLabel lists x = a) ↔ a.2 ∈ lists a.1 := by
  rcases a with ⟨j,a⟩
  constructor
  · rintro ⟨⟨i,k⟩,he⟩
    change (⟨i,(lists i).get k⟩ : Σ j, A j) = ⟨j,a⟩ at he
    obtain ⟨rfl,hget⟩ := Sigma.mk.inj_iff.mp he
    exact (eq_of_heq hget) ▸ List.get_mem _ k
  · intro ha
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp ha
    exact ⟨⟨j,k⟩,congrArg (Sigma.mk j) hk⟩

variable [DecidableEq J] [∀ j, DecidableEq (A j)]

theorem markedMemoryListFamily_scalar (lists : (j : J) → List (A j))
    (hn : ∀ j, (lists j).Nodup) (a : Σ j, A j)
    (value : (Σ j, Fin (lists j).length) → M) (c : M)
    (hc : ∀ x, markedMemoryListFamilyLabel lists x = a → value x = c) :
    (∏ x : (Σ j, Fin (lists j).length),
      if markedMemoryListFamilyLabel lists x = a then value x else 1) =
      if a.2 ∈ lists a.1 then c else 1 := by
  simpa only [markedMemoryListFamilyLabel_mem] using
    markedMemoryScalarFiber_single _ (markedMemoryListFamilyLabel_injective lists hn) a value c hc

end
end ArtinMatthews
