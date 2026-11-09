module

public import ArtinMatthews.GiantSignedEdgeLivePrime


set_option backward.privateInPublic true
@[expose] public section

/-! A live active slot carries residue zero. An old ghost survivor
retains its residue and an appended birth starts at zero. -/
namespace ArtinMatthews
noncomputable section

def giantSignedLiveParticle {P : Finset ℕ} {M : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) :
    GiantSignedLiveSlots M m.1 → GiantSignedParticle P :=
  Sum.elim (fun i => giantSignedParticleAt 0 (active i)) m.2

theorem giantSignedLiveParticle_prime {P : Finset ℕ} {M : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) (s : GiantSignedLiveSlots M m.1) :
    (giantSignedLiveParticle active m s).1 = giantSignedLivePrime active m s := by
  cases s <;> rfl

theorem giantSignedGhostLiveOrigin_particle {P : Finset ℕ} {M b : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (born : Fin b → P) (s : GiantSignedLiveSlots M (giantSignedGhostTarget m deleted born).1) :
    giantSignedLiveParticle active (giantSignedGhostTarget m deleted born) s =
      Sum.elim (giantSignedLiveParticle active m) (fun i => giantSignedParticleAt 0 (born i))
        (giantSignedGhostLiveOrigin M m deleted born s) := by
  rcases s with i | i
  · rfl
  · change Fin ((deletedᶜ).card+b) at i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [giantSignedGhostLiveOrigin_survivor]
      exact giantSignedGhostTarget_survivor m deleted born j
    · intro j
      rw [giantSignedGhostLiveOrigin_born]
      change (giantSignedGhostTarget m deleted born).2 (Fin.natAdd (deletedᶜ).card j) =
        giantSignedParticleAt 0 (born j)
      simpa only [giantSignedParticleAt, Int.cast_zero] using giantSignedGhostTarget_born m deleted born j

end
end ArtinMatthews
