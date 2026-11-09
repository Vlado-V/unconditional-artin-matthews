module

public import ArtinMatthews.GiantSignedChronologicalParticles
public import ArtinMatthews.GiantTwoSidedPatternPathOffsets


set_option backward.privateInPublic true
@[expose] public section

/-! Each particle records displacement from its actual birth visit.
A promotion can reset an anchor only at a congruent offset. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n M : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedBirthOffset (o : Fin (n+1) → ℤ) (d : GiantSignedBirthData PB ell C batch) :
    GiantSignedPerformedBirth d → ℤ
  | .inl _ => o 0
  | .inr (.inl b) => o b.1.succ
  | .inr (.inr b) => o b.1

def giantSignedChronologicalOffset (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : Fin (n+1) → ℤ :=
  giantTwoSidedPathOffset (fun i => κ i * (giantSignedChronologicalProduct h i : ℤ))

def GiantSignedLineageAnchored {d : GiantSignedBirthData PB ell C batch}
    {s : GiantSignedState PS PB M} {g : B} {time : ℕ}
    (o : Fin (n+1) → ℤ) (now : ℤ) (l : GiantSignedBirthLineage d s g time) : Prop :=
  ∀ z, giantSignedStateLiveParticle s g z =
    giantSignedParticleAt (now - giantSignedBirthOffset o d (l.origin z)) (giantSignedStateLivePrime s g z)

private theorem giantSignedStateLiveParticle_ownPrime (s : GiantSignedState PS PB M) (g : B)
    (z : GiantSignedStateLiveSlots s g) {d : ℤ} {p : PB g}
    (h : giantSignedStateLiveParticle s g z = giantSignedParticleAt d p) :
    giantSignedStateLiveParticle s g z = giantSignedParticleAt d (giantSignedStateLivePrime s g z) := by
  have hp : (giantSignedStateLiveParticle s g z).1 = p := congrArg Sigma.fst h
  exact h.trans (congrArg (giantSignedParticleAt d) (hp.symm.trans (giantSignedStateLiveParticle_prime s g z)))

theorem giantSignedChronologicalVisitLineage_anchored
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (o : Fin (n+1) → ℤ)
    (i : Fin (n+1)) (g : B)
    (l : GiantSignedBirthLineage (giantSignedChronologicalBirthData h) (h.state i) g (2*i.val))
    (hl : GiantSignedLineageAnchored o (o i) l) :
    GiantSignedLineageAnchored o (o i) (giantSignedChronologicalVisitLineage h i g l) := by
  intro z
  have hp := giantSignedChronologicalVisitOrigin_particle h i g z
  have ho : (giantSignedChronologicalVisitLineage h i g l).origin z =
      Sum.elim l.origin (giantSignedChronologicalVisitBirth h i g)
        (giantSignedChronologicalVisitOrigin h i g z) := rfl
  cases he : giantSignedChronologicalVisitOrigin h i g z with
  | inl u =>
      simp only [he, Sum.elim_inl] at hp ho
      rw [ho]
      exact giantSignedStateLiveParticle_ownPrime _ _ _ (hp.trans (hl u))
  | inr u =>
      simp only [he, Sum.elim_inr] at hp ho
      rw [ho]
      have hz : o i - giantSignedBirthOffset o (giantSignedChronologicalBirthData h)
          (giantSignedChronologicalVisitBirth h i g u) = 0 := sub_self _
      rw [hz]
      exact giantSignedStateLiveParticle_ownPrime _ _ _ hp

theorem giantSignedChronologicalNextLineage_anchored (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (ha : GiantSignedChronologicalAdmissible κ h) (o : Fin (n+1) → ℤ) (i : Fin n) (g : B)
    (hshift : o i.succ = o i.castSucc + κ i * (giantSignedChronologicalProduct h i : ℤ))
    (l : GiantSignedBirthLineage (giantSignedChronologicalBirthData h)
      (giantSignedChronologicalAfterVisitState h i.castSucc) g (2*i.castSucc.val+1))
    (hl : GiantSignedLineageAnchored o (o i.castSucc) l) :
    GiantSignedLineageAnchored o (o i.succ) (giantSignedChronologicalNextLineage h κ ha i g l) := by
  intro z
  have hp := giantSignedChronologicalEdgeOrigin_particle κ h ha i g z
  have ho : (giantSignedChronologicalNextLineage h κ ha i g l).origin z =
      Sum.elim l.origin (giantSignedChronologicalEdgeBirth h i g)
        (giantSignedChronologicalEdgeOrigin κ h ha.compatible i g z) := rfl
  cases he : giantSignedChronologicalEdgeOrigin κ h ha.compatible i g z with
  | inl u =>
      simp only [he, Sum.elim_inl] at hp ho
      rw [ho]
      apply giantSignedStateLiveParticle_ownPrime _ _ _
      refine hp.trans ((congrArg (giantSignedParticleTranslate
        (κ i * (giantSignedChronologicalProduct h i : ℤ))) (hl u)).trans ?_)
      rw [giantSignedParticleTranslate_at, hshift]
      congr 1
      ring
  | inr u =>
      simp only [he, Sum.elim_inr] at hp ho
      rw [ho]
      have hz : o i.succ - giantSignedBirthOffset o (giantSignedChronologicalBirthData h)
          (giantSignedChronologicalEdgeBirth h i g u) = 0 := sub_self _
      rw [hz]
      exact giantSignedStateLiveParticle_ownPrime _ _ _ hp

theorem giantSignedChronologicalPreLineage_anchored (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (ha : GiantSignedChronologicalAdmissible κ h) (i : Fin (n+1)) (g : B) :
    GiantSignedLineageAnchored (giantSignedChronologicalOffset κ h)
      (giantSignedChronologicalOffset κ h i) (giantSignedChronologicalPreLineage h κ ha i g) := by
  let o := giantSignedChronologicalOffset κ h
  change GiantSignedLineageAnchored o (o i) _
  induction i using Fin.induction with
  | zero =>
      intro z
      rcases z with z | z
      · change giantSignedParticleAt 0 ((h.state 0).2.1 g z) =
          giantSignedParticleAt (o 0-o 0) ((h.state 0).2.1 g z)
        rw [sub_self]
      · have h0 : (h.state 0).2.2.1 g = 0 :=
          congrArg (fun m : GiantSignedMemory PB => m.1 g) ha.boundary.1
        have hz := z.isLt
        omega
  | succ i ih =>
      have hshift : o i.succ = o i.castSucc + κ i * (giantSignedChronologicalProduct h i : ℤ) :=
        giantTwoSidedPathOffset_succ _ i
      exact giantSignedChronologicalNextLineage_anchored κ h ha o i g hshift _
        (giantSignedChronologicalVisitLineage_anchored h o i.castSucc g _ ih)

end
end ArtinMatthews
