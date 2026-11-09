module

public import ArtinMatthews.MarkedMemoryActivePathData
public import ArtinMatthews.MarkedMemoryIndependentLineExpectation


set_option backward.privateInPublic true
@[expose] public section

/-! Disjoint numeric prime bands identify the typed band-prime carrier
with the literal union. Active visits in the independent-line observable
then agree with the actual per-band active path. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset Nat.Primes)

def markedMemoryBandPrimeUnion : Finset Nat.Primes := Finset.univ.biUnion P

def markedMemoryBandPrimeEquiv (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) :
    (Σ j,↥(P j)) ≃ ↥(markedMemoryBandPrimeUnion P) :=
  Equiv.ofBijective
    (fun a => ⟨a.2.1,Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,a.2.2⟩⟩)
    ⟨by
      rintro ⟨i,a⟩ ⟨j,b⟩ he
      have hp : a.1=b.1 := congrArg Subtype.val he
      have hij : i=j := by
        by_contra hn
        exact (Finset.disjoint_left.mp (hP i j hn)) a.2 (hp.symm ▸ b.2)
      subst j
      have hab : a=b := Subtype.ext hp
      cases hab
      rfl,
     by
      intro p
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp p.2
      exact ⟨⟨j,⟨p.1,hj⟩⟩,rfl⟩⟩

variable {P} {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (d : MarkedMemoryActivePathData P pads Z n)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))

include hP in
theorem markedMemoryActiveVisits_eq_path (j : J) (p : P j) :
    markedMemoryActiveVisits (fun v i k => d.active v i k) p.1=markedMemoryPathVisits d j p := by
  ext v
  simp only [markedMemoryActiveVisits,markedMemoryPathVisits,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,k,hk⟩
    have hij : i=j := by
      by_contra hn
      exact (Finset.disjoint_left.mp (hP i j hn)) (d.active v i k).2 (hk.symm ▸ p.2)
    subst i
    exact ⟨k,Subtype.ext hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨j,k,congrArg Subtype.val hk⟩

end
end ArtinMatthews
