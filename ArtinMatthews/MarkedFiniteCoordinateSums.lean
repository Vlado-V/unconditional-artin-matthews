module

public import ArtinMatthews.MarkedPhysicalFiniteTargetCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Finite coordinate sums with genuine zero extension. The change of
finite carrier is constructed pointwise on the actual nonzero support. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedFiniteCoordinateSum_eq {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (G T : Finset α) (f : (ι → α) → ℂ)
    (hG : ∀ x,f x≠0 → ∀ i,x i∈G) (hT : ∀ x,f x≠0 → ∀ i,x i∈T) :
    (∑ x : ι → G,f (fun i => (x i).1))=
      ∑ x : ι → T,f (fun i => (x i).1) := by
  apply Finset.sum_bij_ne_zero
    (fun x _ hx i => (⟨(x i).1,hT (fun j => (x j).1) hx i⟩ : T))
  · intro x _ _
    exact Finset.mem_univ _
  · intro x _ _ y _ _ he
    funext i
    apply Subtype.ext
    exact congrArg (fun a => (a i).1) he
  · intro y _ hy
    let x : ι → G := fun i => ⟨(y i).1,hG (fun j => (y j).1) hy i⟩
    exact ⟨x,Finset.mem_univ _,hy,rfl⟩
  · intro x _ _
    rfl

end
end ArtinMatthews
