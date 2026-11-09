module

public import ArtinMatthews.GiantSignedBirthDisplacement


set_option backward.privateInPublic true
@[expose] public section

/-! Active slots and selected ghost terminations hit the residue of
their actual birth. Distinct births identify the anchor across visits. -/
namespace ArtinMatthews
noncomputable section

private theorem giantSignedParticle_eq_at_zero {P : Finset ℕ} (z : GiantSignedParticle P)
    (hz : z.2 = 0) : z = giantSignedParticleAt 0 z.1 := by
  rcases z with ⟨p,r⟩
  change r = 0 at hz
  simp only [giantSignedParticleAt, Int.cast_zero, hz]

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (κ : Fin n → ℤ) (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (ha : GiantSignedChronologicalAdmissible κ h)

theorem giantSignedChronological_zero_anchor (i : Fin (n+1)) (g : B)
    (z : GiantSignedStateLiveSlots (h.state i) g)
    (hz : (giantSignedStateLiveParticle (h.state i) g z).2 = 0) :
    let p := (giantSignedStateLivePrime (h.state i) g z).val
    let o := giantSignedChronologicalOffset κ h
    let b := (giantSignedChronologicalPreLineage h κ ha i g).origin z
    (o i : ZMod p) = (giantSignedBirthOffset o (giantSignedChronologicalBirthData h) b : ZMod p) := by
  let o := giantSignedChronologicalOffset κ h
  let b := (giantSignedChronologicalPreLineage h κ ha i g).origin z
  let u := giantSignedBirthOffset o (giantSignedChronologicalBirthData h) b
  let p := giantSignedStateLivePrime (h.state i) g z
  have hp : giantSignedStateLiveParticle (h.state i) g z = giantSignedParticleAt (o i-u) p :=
    giantSignedChronologicalPreLineage_anchored κ h ha i g z
  have hzero : giantSignedStateLiveParticle (h.state i) g z = giantSignedParticleAt 0 p :=
    (giantSignedParticle_eq_at_zero _ hz).trans
      (congrArg (giantSignedParticleAt 0) (giantSignedStateLiveParticle_prime (h.state i) g z))
  have hr : giantSignedParticleAt 0 p = giantSignedParticleAt (o i-u) p := hzero.symm.trans hp
  have hc : ((0:ℤ) : ZMod p.val) = ((o i-u:ℤ) : ZMod p.val) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hr).2
  rw [Int.cast_zero, Int.cast_sub] at hc
  exact sub_eq_zero.mp hc.symm

theorem giantSignedChronological_active_anchor (i : Fin (n+1)) (g : B) (j : Fin (k+ell)) :
    let p := ((h.state i).2.1 g j).val
    let o := giantSignedChronologicalOffset κ h
    let b := (giantSignedChronologicalPreLineage h κ ha i g).origin (.inl j)
    (o i : ZMod p) = (giantSignedBirthOffset o (giantSignedChronologicalBirthData h) b : ZMod p) :=
  giantSignedChronological_zero_anchor κ h ha i g (.inl j) (Int.cast_zero)

theorem giantSignedChronological_deleted_anchor (i : Fin (n+1)) (g : B)
    (j : Fin ((h.state i).2.2.1 g)) (hj : j ∈ h.deleted i g) :
    let p := ((h.state i).2.2.2 g j).1.val
    let o := giantSignedChronologicalOffset κ h
    let b := (giantSignedChronologicalPreLineage h κ ha i g).origin (.inr j)
    (o i : ZMod p) = (giantSignedBirthOffset o (giantSignedChronologicalBirthData h) b : ZMod p) := by
  apply giantSignedChronological_zero_anchor κ h ha i g (.inr j)
  have hz := ha.deletedZeros i g hj
  unfold giantSignedGhostZeroIndices at hz
  exact (Finset.mem_filter.mp hz).2

include ha in
theorem giantSignedChronological_active_offsets (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (i j : Fin (n+1)) (g f : B) (u v : Fin (k+ell))
    (hp : ((h.state i).2.1 g u).val = ((h.state j).2.1 f v).val) :
    (giantSignedChronologicalOffset κ h i : ZMod ((h.state i).2.1 g u).val) =
      (giantSignedChronologicalOffset κ h j : ZMod ((h.state i).2.1 g u).val) := by
  let l := giantSignedChronologicalPreLineage h κ ha i g
  let m := giantSignedChronologicalPreLineage h κ ha j f
  have he : l.origin (.inl u) = m.origin (.inl v) :=
    hd ((l.prime_eq (.inl u)).trans (hp.trans (m.prime_eq (.inl v)).symm))
  have h1 := giantSignedChronological_active_anchor κ h ha i g u
  have h2 := giantSignedChronological_active_anchor κ h ha j f v
  let o := giantSignedChronologicalOffset κ h
  let b := giantSignedBirthOffset o (giantSignedChronologicalBirthData h)
  change (o i : ZMod ((h.state i).2.1 g u).val) =
    (b (l.origin (.inl u)) : ZMod ((h.state i).2.1 g u).val) at h1
  change (o j : ZMod ((h.state j).2.1 f v).val) =
    (b (m.origin (.inl v)) : ZMod ((h.state j).2.1 f v).val) at h2
  rw [he] at h1
  exact h1.trans ((hp.symm ▸ h2 : (o j : ZMod ((h.state i).2.1 g u).val) =
    (b (m.origin (.inl v)) : ZMod ((h.state i).2.1 g u).val))).symm

end
end ArtinMatthews
