module

public import ArtinMatthews.MarkedMemoryLabelOrbit
public import ArtinMatthews.MarkedMemoryFiniteTableauRecovery


set_option backward.privateInPublic true
@[expose] public section

/-! Freeness also holds for names transported between different finite
carriers. It follows from actual used-ID coverage, not prime injectivity. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A C : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  [∀ j,Fintype (C j)] [∀ j,DecidableEq (C j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryFinite_labeling_injective :
    Function.Injective (fun e : (j : J) → A j ≃ C j =>
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e d)) := by
  intro e f h
  have hr := congrArg (markedMemoryFiniteTableau_toIndependent hZ) h
  have hactive (v : ℕ) (hv : v≤n) (j : J) (k : Fin (pads+1)) :
      e j (d.activeId v j k)=f j (d.activeId v j k) := by
    have hh := congrArg (fun z : MarkedMemoryIndependentLifespans
      (A := C) (P := P) (pads := pads) (B := B) hZ n => z.activeId v j k) hr
    simpa only [markedMemoryFinite_restore_activeId hZ _ v hv j,markedMemoryIndependentRelabel,
      Function.Embedding.trans_apply,Equiv.toEmbedding_apply] using hh
  have hqueue (t : ℕ) (ht : t≤2*n+1) (j : J) :
      (markedMemoryIndependentQueue hZ d t j).map (e j)=
        (markedMemoryIndependentQueue hZ d t j).map (f j) := by
    have hh := congrArg (fun z : MarkedMemoryIndependentLifespans
      (A := C) (P := P) (pads := pads) (B := B) hZ n => markedMemoryIndependentQueue hZ z t j) hr
    simpa only [markedMemoryFinite_restore_queue hZ _ t ht j,markedMemoryIndependentRelabel_queue] using hh
  funext j
  apply Equiv.ext
  intro a
  obtain ⟨t,ht,ha | ha⟩ := markedMemoryIndependent_label_used hZ d j a
  · obtain ⟨k,rfl⟩ := ha
    exact hactive (t/2) (by omega) j k
  · exact List.map_inj_left.mp (hqueue t ht j) a ha

end
end ArtinMatthews
