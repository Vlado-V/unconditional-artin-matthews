module

public import ArtinMatthews.GiantSignedEdgeEquivariance


set_option backward.privateInPublic true
@[expose] public section

/-! Actual target-memory transport under relabelling old promotion indices. -/
namespace ArtinMatthews
noncomputable section

theorem giantSignedEdgeTarget_symmetric_test {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) (σ : (j : J) → Equiv.Perm (Fin (m.1 j)))
    (f : GiantSignedMemory P → ℂ) (hf : GiantSignedMemorySymmetric f) :
    f (giantSignedEdgeTarget d (giantSignedMemoryPermute m σ) source c) =
      f (giantSignedEdgeTarget d m source
        ⟨c.1, c.2.1, fun j => giantSignedMovedPromotion (σ j) (c.2.2 j)⟩) := by
  let c' : GiantSignedEdgeChoice t m.1 :=
    ⟨c.1, c.2.1, fun j => giantSignedMovedPromotion (σ j) (c.2.2 j)⟩
  let left := giantSignedEdgeTarget d (giantSignedMemoryPermute m σ) source c
  let right := giantSignedEdgeTarget d m source c'
  let E (j : J) : Fin (left.1 j) ≃ Fin (right.1 j) :=
    giantSignedOutputOrderEquiv (σ j) (c.2.2 j) (c.1 j).card
  have ht : left.2 = fun j i => right.2 j (E j i) := by
    funext j i
    refine Fin.addCases ?_ ?_ i
    · intro k
      dsimp only [E]
      erw [giantSignedOutputOrderEquiv_left]
      dsimp only [left, right]
      erw [giantSignedEdgeTarget_survivor d (giantSignedMemoryPermute m σ) source c j k,
        giantSignedEdgeTarget_survivor d m source c' j
          (giantSignedComplementOrderEquiv (σ j) (c.2.2 j) k)]
      change giantSignedParticleTranslate d
          (m.2 j (σ j (((Finset.univ.map (c.2.2 j))ᶜ).orderEmbOfFin rfl k))) =
        giantSignedParticleTranslate d
          (m.2 j (((Finset.univ.map (giantSignedMovedPromotion (σ j) (c.2.2 j)))ᶜ).orderEmbOfFin rfl
            (giantSignedComplementOrderEquiv (σ j) (c.2.2 j) k)))
      exact congrArg (fun i => giantSignedParticleTranslate d (m.2 j i))
        (giantSignedComplementOrderEquiv_apply (σ j) (c.2.2 j) k).symm
    · intro k
      dsimp only [E]
      erw [giantSignedOutputOrderEquiv_right]
      dsimp only [left, right]
      erw [giantSignedEdgeTarget_store d (giantSignedMemoryPermute m σ) source c j k,
        giantSignedEdgeTarget_store d m source c' j k]
  change f left = f right
  calc
    f left = f ⟨left.1, fun j i => right.2 j (E j i)⟩ := by
      have h := congrArg (fun u => (⟨left.1, u⟩ : GiantSignedMemory P)) ht
      exact congrArg f h
    _ = f right := giantSignedMemorySymmetric_equiv f hf E right.2

theorem giantSignedEdgeHits_permute {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (target : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) (σ : (j : J) → Equiv.Perm (Fin (m.1 j))) :
    GiantSignedEdgeHits d (giantSignedMemoryPermute m σ) target c ↔
      GiantSignedEdgeHits d m target
        ⟨c.1, c.2.1, fun j => giantSignedMovedPromotion (σ j) (c.2.2 j)⟩ := Iff.rfl

end
end ArtinMatthews
