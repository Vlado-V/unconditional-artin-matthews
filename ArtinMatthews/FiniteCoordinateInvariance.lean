module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Coordinatewise invariance implies invariance under a simultaneous
finite family of permitted replacements. -/
namespace ArtinMatthews
noncomputable section

def finiteCoordinateReplace {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (s : Finset ι) (x y : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ s then y i else x i

@[simp] theorem finiteCoordinateReplace_empty {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (x y : ∀ i, X i) : finiteCoordinateReplace ∅ x y = x := by
  funext i
  simp [finiteCoordinateReplace]

@[simp] theorem finiteCoordinateReplace_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} (x y : ∀ i, X i) : finiteCoordinateReplace Finset.univ x y = y := by
  funext i
  simp [finiteCoordinateReplace]

theorem finiteCoordinateReplace_insert {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (s : Finset ι) (j : ι) (x y : ∀ i, X i) :
    finiteCoordinateReplace (insert j s) x y =
      Function.update (finiteCoordinateReplace s x y) j (y j) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [finiteCoordinateReplace]
  · simp [finiteCoordinateReplace, hi]

theorem finiteCoordinateInvariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} {T : Type*} (R : ∀ i, X i → X i → Prop)
    (F : (∀ i, X i) → T)
    (hF : ∀ x i t, R i (x i) t → F (Function.update x i t) = F x)
    (x y : ∀ i, X i) (hxy : ∀ i, R i (x i) (y i)) : F y = F x := by
  have h : ∀ s : Finset ι, F (finiteCoordinateReplace s x y) = F x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [finiteCoordinateReplace_empty]
    | @insert i s hi ih =>
      rw [finiteCoordinateReplace_insert]
      have hr : R i ((finiteCoordinateReplace s x y) i) (y i) := by
        simpa only [finiteCoordinateReplace, hi, ite_false] using hxy i
      exact (hF _ i _ hr).trans ih
  simpa only [finiteCoordinateReplace_univ] using h Finset.univ

end
end ArtinMatthews
