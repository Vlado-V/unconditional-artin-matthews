module

public import ArtinMatthews.MarkedMemoryCappedFiberCoordinates
public import ArtinMatthews.MarkedMemoryCappedLabelUnique


set_option backward.privateInPublic true
@[expose] public section

/-! The unlabelled capped path/decorations assembly is injective.
Full-tableau extraction determines the path and copied order, while
canonical prime labels determine the remaining relabeling and births. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

include hempty in
theorem markedMemoryCappedPathDecoratedAssembly_injective :
    Function.Injective (markedMemoryCappedPathDecoratedAssembly (n := n) hZ hP s) := by
  intro i j hij
  let H := markedMemoryCappedPathSupportedAssembly hZ hP s i
  have hi : markedMemoryCappedPathDecoratedAssembly hZ hP s i=H.1 := rfl
  have hj : markedMemoryCappedPathDecoratedAssembly hZ hP s j=H.1 := hij.symm
  have ci := markedMemoryCappedFiber_coordinates hZ hP s hempty H i hi
  have cj := markedMemoryCappedFiber_coordinates hZ hP s hempty H j hj
  have hp : i.1=j.1 := markedMemoryCappedPathIndex_ext hZ s
    (ci.1.trans cj.1.symm) (ci.2.1.trans cj.2.1.symm)
  have ho : i.2.2=j.2.2 := ci.2.2.trans cj.2.2.symm
  obtain ⟨ei,fi,_⟩ := markedMemoryCappedPathFiber_extraction hZ hP s i hempty H.1 H.2.1 hi
  obtain ⟨ej,fj,_⟩ := markedMemoryCappedPathFiber_extraction hZ hP s j hempty H.1 H.2.1 hj
  rcases i with ⟨u,bi,oi⟩
  rcases j with ⟨v,bj,oj⟩
  change u=v at hp
  cases hp
  have he : ei=ej := markedMemoryCappedLabel_unique (B := B) hZ
    (markedMemoryActualTableau hZ H.1 H.2.1) u.path u.choices u.compatible u.capacity bi bj ei ej fi fj
  have ht : markedMemoryCappedPathTableau (B := B) hZ u.path u.choices u.compatible u.capacity bi=
      markedMemoryCappedPathTableau (B := B) hZ u.path u.choices u.compatible u.capacity bj :=
    fi.symm.trans ((congrArg (fun e => markedMemoryIndependent_toFinite hZ
      (markedMemoryIndependentRelabel hZ e (markedMemoryActualTableau hZ H.1 H.2.1))) he).trans fj)
  have hb := markedMemoryEndpointBirthOrders_decorate_injective
    (markedMemoryPathEndpointData hZ u.path u.choices u.compatible)
    ((markedMemoryCappedPathTableau_data (B := B) hZ u.path u.choices u.compatible u.capacity bi).symm.trans
      ((congrArg Subtype.val ht).trans
        (markedMemoryCappedPathTableau_data (B := B) hZ u.path u.choices u.compatible u.capacity bj)))
  change oi=oj at ho
  cases hb
  cases ho
  rfl

end
end ArtinMatthews
