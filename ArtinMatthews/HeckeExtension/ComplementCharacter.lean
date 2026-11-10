module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Bound.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal projection for complementary subgroups of a commutative group. -/
namespace ArtinMatthews
noncomputable section
variable {G : Type*} [CommGroup G] {H : Type*} [Monoid H]

def complementProductEquiv (E B : Subgroup G) (h : IsCompl E B) : E × B ≃* G :=
  MulEquiv.ofBijective (E.subtype.coprod B.subtype) ⟨
    Subgroup.mul_injective_of_disjoint h.disjoint, fun g => by
      have hg : g ∈ E ⊔ B := by rw [h.sup_eq_top]; exact Subgroup.mem_top g
      obtain ⟨e, b, he⟩ := Subgroup.mem_sup'.mp hg
      exact ⟨(e, b), he⟩⟩

def complementProjection (E B : Subgroup G) (h : IsCompl E B) : G →* B :=
  (MonoidHom.snd E B).comp (complementProductEquiv E B h).symm.toMonoidHom

@[simp] theorem complementProjection_right (E B : Subgroup G) (h : IsCompl E B) (b : B) :
    complementProjection E B h b.val = b := by
  let e := complementProductEquiv E B h
  have he : e.symm b.val = (1, b) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change b.val = 1 * b.val
    exact (one_mul _).symm
  exact congrArg Prod.snd he

theorem complementProjection_left (E B : Subgroup G) (h : IsCompl E B) (a : E) :
    complementProjection E B h a.val = 1 := by
  let e := complementProductEquiv E B h
  have he : e.symm a.val = (a, 1) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change a.val = a.val * 1
    exact (mul_one _).symm
  exact congrArg Prod.snd he

def complementCharacter (E B : Subgroup G) (h : IsCompl E B) (χ : B →* H) : G →* H :=
  χ.comp (complementProjection E B h)

@[simp] theorem complementCharacter_right (E B : Subgroup G) (h : IsCompl E B)
    (χ : B →* H) (b : B) : complementCharacter E B h χ b.val = χ b := by
  simp [complementCharacter]

theorem complementCharacter_left (E B : Subgroup G) (h : IsCompl E B)
    (χ : B →* H) (a : E) : complementCharacter E B h χ a.val = 1 := by
  simp [complementCharacter, complementProjection_left E B h a]

end
end ArtinMatthews
