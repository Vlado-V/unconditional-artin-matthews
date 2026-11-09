module

public import ArtinMatthews.MarkedInjectedBirthMass


set_option backward.privateInPublic true
@[expose] public section

/-! The original natural-number band and its prime subtype have the
same draws. The equivalence preserves each numerical prime exactly. -/
namespace ArtinMatthews
noncomputable section

def giantSignedTypedPrimeBandEmbedding (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ↥P ↪ Nat.Primes where
  toFun p := ⟨p.val,hP p.val p.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun p : Nat.Primes => p.val) h)

def giantSignedTypedPrimeBand (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : Finset Nat.Primes :=
  P.attach.map (giantSignedTypedPrimeBandEmbedding P hP)

def giantSignedTypedPrimeBandEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ↥P ≃ ↥(giantSignedTypedPrimeBand P hP) :=
  Equiv.ofBijective (fun p => ⟨giantSignedTypedPrimeBandEmbedding P hP p, by
    change _ ∈ P.attach.map (giantSignedTypedPrimeBandEmbedding P hP)
    exact Finset.mem_map.mpr ⟨p,Finset.mem_attach _ _,rfl⟩⟩) (by
      constructor
      · intro p q h
        exact Subtype.ext (congrArg (fun a : ↥(giantSignedTypedPrimeBand P hP) => a.val.val) h)
      · intro p
        have hp := p.property
        change p.val ∈ P.attach.map (giantSignedTypedPrimeBandEmbedding P hP) at hp
        obtain ⟨q,_,hq⟩ := Finset.mem_map.mp hp
        exact ⟨q,Subtype.ext hq⟩)

theorem giantSignedTypedPrimeBandEquiv_value (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (p : P) :
    (giantSignedTypedPrimeBandEquiv P hP p).val = ⟨p.val,hP p.val p.property⟩ :=
  rfl

end
end ArtinMatthews
