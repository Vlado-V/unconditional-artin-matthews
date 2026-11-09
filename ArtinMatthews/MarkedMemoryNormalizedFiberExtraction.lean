module

public import ArtinMatthews.MarkedMemoryNormalizedReverseExtraction
public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
public import ArtinMatthews.MarkedMemoryFiniteTableauInjective


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual normalized fiber member is a genuine relabeling of
canonical extraction. The finite wrapper removes unused time tails;
the birth-anchor convention removes unused static-anchor freedom. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryNormalizedFiber_extraction
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s)
    (hi : markedMemoryNormalizedHistoryAssembly hZ s i=history) :
    ∃ e : (j : J) → MarkedMemoryActualFiber hZ history j ≃ A j,
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e
        (markedMemoryActualTableau hZ history ha))=i.1.1.1 ∧
          markedMemoryActualOrder hZ history ha=i.1.2 := by
  rcases i with ⟨⟨⟨f,hs⟩,order⟩,hn⟩
  let d := markedMemoryFiniteTableau_toIndependent hZ f
  have hdn : MarkedMemoryBirthNormalized hZ d :=
    (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ f).mp hn
  change markedMemoryIndependentState hZ d 0 (Nat.zero_le n)=s at hs
  cases hs
  change markedMemoryIndependentHistory hZ d order=history at hi
  subst history
  refine ⟨markedMemoryBandAddressEquiv hZ d order,?_,?_⟩
  · exact (markedMemoryNormalized_reverse_extraction hZ d order hempty hdn ha).trans
      (markedMemoryFiniteTableau_restrict_extend hZ f)
  · exact markedMemoryNormalized_reverse_order hZ d order hempty hdn ha

end
end ArtinMatthews
