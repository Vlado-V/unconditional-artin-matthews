module

public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical extension is faithful on the finite tableaux: restricting
it again gives the same finite data, including all birth/queue ordering. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

theorem markedMemoryFiniteTableau_restrict_extend
    (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n) :
    markedMemoryIndependent_toFinite hZ (markedMemoryFiniteTableau_toIndependent hZ f)=f := by
  apply Subtype.ext
  apply MarkedMemoryFiniteTableauData.ext
  · funext j a
    apply Fin.ext
    rfl
  · funext j a
    apply Fin.ext
    rfl
  · funext t j
    ext a
    simp [markedMemoryIndependent_toFinite,markedMemoryFiniteData_ofIndependent,
      markedMemoryFiniteTableau_toIndependent,markedMemoryFiniteQueue]
    constructor
    · intro h
      exact (f.1.activeAt_valid t j a).mp (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,(f.1.activeAt_valid t j a).mpr h⟩
  · funext j
    apply markedMemoryFiniteList_toList_injective
    simp [markedMemoryIndependent_toFinite,markedMemoryFiniteData_ofIndependent,markedMemoryFiniteTableau_toIndependent,
      markedMemoryFiniteQueue,MarkedMemoryFiniteTableauData.initialAt]
  · funext v j
    apply markedMemoryFiniteList_toList_injective
    simp [markedMemoryIndependent_toFinite,markedMemoryFiniteData_ofIndependent,markedMemoryFiniteTableau_toIndependent,
      markedMemoryFiniteQueue]
  · funext v j
    change f.1.incomingAt (2*v.val+1) j=f.1.incoming v j
    exact f.1.incomingAt_valid v j
  · funext v j
    change f.1.outgoingAt (2*v.val+1) j=f.1.outgoing v j
    exact f.1.outgoingAt_valid v j
  · funext v
    change f.1.positionAt v.val=f.1.position v
    exact f.1.positionAt_valid v
  · funext v j
    change f.1.activeIdAt v.val j=f.1.activeId v j
    exact f.1.activeIdAt_valid v j
  · rfl

theorem markedMemoryFiniteTableau_toIndependent_injective :
    Function.Injective (markedMemoryFiniteTableau_toIndependent (A := A) (P := P)
      (pads := pads) (B := B) (n := n) hZ) := by
  intro f g h
  have hh := congrArg (markedMemoryIndependent_toFinite hZ) h
  simpa only [markedMemoryFiniteTableau_restrict_extend] using hh

end
end ArtinMatthews
