module

public import ArtinMatthews.GiantSignedGhostRawSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Permuting an old ordered memory transports its actual deletion
subsets and the survivor order. The complete ghost preserves symmetry. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedGhostSurvivorEquiv {k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) : ↥(Sᶜ) ≃ ↥((S.map σ.toEmbedding)ᶜ) where
  toFun i := ⟨σ i, by simpa only [Finset.mem_compl, Finset.mem_map_equiv,
    Equiv.symm_apply_apply] using i.property⟩
  invFun i := ⟨σ.symm i, by simpa only [Finset.mem_compl, Finset.mem_map_equiv] using i.property⟩
  left_inv _ := Subtype.ext (σ.symm_apply_apply _)
  right_inv _ := Subtype.ext (σ.apply_symm_apply _)

def giantSignedGhostSurvivorIndexEquiv {k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) : Fin (Sᶜ).card ≃ Fin ((S.map σ.toEmbedding)ᶜ).card :=
  ((Sᶜ).orderIsoOfFin rfl).toEquiv.trans
    ((giantSignedGhostSurvivorEquiv σ S).trans
      (((S.map σ.toEmbedding)ᶜ).orderIsoOfFin rfl).toEquiv.symm)

theorem giantSignedGhostSurvivorIndexEquiv_spec {k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) (i : Fin (Sᶜ).card) :
    ((S.map σ.toEmbedding)ᶜ).orderEmbOfFin rfl (giantSignedGhostSurvivorIndexEquiv σ S i) =
      σ ((Sᶜ).orderEmbOfFin rfl i) := by
  let e := (((S.map σ.toEmbedding)ᶜ).orderIsoOfFin rfl).toEquiv
  have h := e.apply_symm_apply (giantSignedGhostSurvivorEquiv σ S (((Sᶜ).orderIsoOfFin rfl) i))
  exact congrArg Subtype.val h

def giantSignedGhostAppendEquiv {n m : ℕ} (e : Fin n ≃ Fin m) (b : ℕ) :
    Fin (n+b) ≃ Fin (m+b) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin b))).trans finSumFinEquiv)

theorem giantSignedGhostAppendEquiv_left {n m : ℕ} (e : Fin n ≃ Fin m) (b : ℕ) (i : Fin n) :
    giantSignedGhostAppendEquiv e b (Fin.castAdd b i) = Fin.castAdd b (e i) := by
  simp [giantSignedGhostAppendEquiv]

theorem giantSignedGhostAppendEquiv_right {n m : ℕ} (e : Fin n ≃ Fin m) (b : ℕ) (i : Fin b) :
    giantSignedGhostAppendEquiv e b (Fin.natAdd n i) = Fin.natAdd m i := by
  simp [giantSignedGhostAppendEquiv]

theorem giantSignedGroupSymmetric_equiv {P : Finset ℕ}
    (f : GiantSignedGroupMemory P → ℂ) (hf : GiantSignedGroupSymmetric f)
    {n m : ℕ} (a : Fin n → GiantSignedParticle P) (b : Fin m → GiantSignedParticle P)
    (e : Fin n ≃ Fin m) (he : a = b ∘ e) : f ⟨n, a⟩ = f ⟨m, b⟩ := by
  have hnm : n = m := by simpa using Fintype.card_congr e
  cases hnm
  rw [he]
  exact hf n e b

theorem giantSignedGhostTarget_symmetric {P : Finset ℕ}
    (f : GiantSignedGroupMemory P → ℂ) (hf : GiantSignedGroupSymmetric f)
    {k b : ℕ} (a : Fin k → GiantSignedParticle P) (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) (β : Fin b → P) :
    f (giantSignedGhostTarget ⟨k, a ∘ σ⟩ S β) =
      f (giantSignedGhostTarget ⟨k, a⟩ (S.map σ.toEmbedding) β) := by
  apply giantSignedGroupSymmetric_equiv f hf _ _
    (giantSignedGhostAppendEquiv (giantSignedGhostSurvivorIndexEquiv σ S) b)
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply, giantSignedGhostAppendEquiv_left,
      Fin.append_left, markedRawSubsetTupleEquiv_survivor,
      giantSignedGhostSurvivorIndexEquiv_spec]
  · intro j
    simp only [Function.comp_apply, giantSignedGhostAppendEquiv_right, Fin.append_right]

theorem giantSignedGhostZeroIndices_map {P : Finset ℕ} {k : ℕ}
    (a : Fin k → GiantSignedParticle P) (σ : Equiv.Perm (Fin k)) :
    (giantSignedGhostZeroIndices ⟨k, a ∘ σ⟩).map σ.toEmbedding =
      giantSignedGhostZeroIndices ⟨k, a⟩ := by
  classical
  ext i
  simp only [Finset.mem_map_equiv, giantSignedGhostZeroIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.comp_apply]
  exact Iff.of_eq (congrArg (fun z : GiantSignedParticle P => z.2 = 0)
    (congrArg a (σ.apply_symm_apply i)))

theorem giantSignedGhostGroupApply_symmetric {P : Finset ℕ}
    (ν : P → ℝ) (A C D : ℂ) (f : GiantSignedGroupMemory P → ℂ)
    (hf : GiantSignedGroupSymmetric f) :
    GiantSignedGroupSymmetric (giantSignedGhostGroupApply ν A C D f) := by
  classical
  intro k σ a
  have hz := giantSignedGhostZeroIndices_map a σ
  have hc : (giantSignedGhostZeroIndices ⟨k, a ∘ σ⟩).card =
      (giantSignedGhostZeroIndices ⟨k, a⟩).card := by
    rw [← hz, Finset.card_map]
  unfold giantSignedGhostGroupApply
  dsimp only
  rw [← giantSignedGhost_subset_sum, ← giantSignedGhost_subset_sum]
  calc
    _ = ∑ S : Finset (Fin k),
        if S.map σ.toEmbedding ⊆ giantSignedGhostZeroIndices ⟨k, a⟩ then
          D ^ (S.map σ.toEmbedding).card *
            A ^ ((giantSignedGhostZeroIndices ⟨k, a⟩).card - (S.map σ.toEmbedding).card) *
            ∑' b, (C ^ b / (Nat.factorial b : ℂ)) * ∑ β : Fin b → P,
              (∏ i, (ν (β i) : ℂ)) *
                f (giantSignedGhostTarget ⟨k, a⟩ (S.map σ.toEmbedding) β)
        else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      have hS : S ⊆ giantSignedGhostZeroIndices ⟨k, a ∘ σ⟩ ↔
          S.map σ.toEmbedding ⊆ giantSignedGhostZeroIndices ⟨k, a⟩ := by
        rw [← hz]
        exact (Finset.map_subset_map).symm
      simp only [hS, Finset.card_map, hc]
      split_ifs
      · congr 1
        apply tsum_congr
        intro b
        congr 1
        apply Finset.sum_congr rfl
        intro β _
        rw [giantSignedGhostTarget_symmetric f hf a σ S β]
      · rfl
    _ = _ := by
      apply Finset.sum_equiv (Equiv.finsetCongr σ)
      · intro S
        simp only [Finset.mem_univ]
      · intro S _
        rfl

end
end ArtinMatthews
