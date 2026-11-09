module

public import ArtinMatthews.GiantSignedEdgeMemory
public import ArtinMatthews.GiantSignedEdgePermutation
public import ArtinMatthews.GiantSignedEdgeRetrieval


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical joint source and target memories retain both pending factors.
Translation preserves the prime law and reverses the two endpoint memories. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedTupleTranslate {J : Type*} {P : J → Finset ℕ} (d : ℤ) (n : J → ℕ) :
    ((j : J) → Fin (n j) → GiantSignedParticle (P j)) ≃
      ((j : J) → Fin (n j) → GiantSignedParticle (P j)) :=
  Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => giantSignedParticleTranslate d

theorem giantSignedTupleTranslate_mass {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (ν : (j : J) → P j → ℂ) (d : ℤ) {n : J → ℕ}
    (u : (j : J) → Fin (n j) → GiantSignedParticle (P j)) :
    (∏ j, ∏ i, ν j (giantSignedTupleTranslate d n u j i).1) =
      ∏ j, ∏ i, ν j (u j i).1 := rfl

theorem giantSignedGroupZeroCount_permute {P : Finset ℕ} {n : ℕ}
    (u : Fin n → GiantSignedParticle P) (σ : Equiv.Perm (Fin n)) :
    giantSignedGroupZeroCount (u ∘ σ) = giantSignedGroupZeroCount u := by
  classical
  rw [giantSignedGroupZeroCount_sum, giantSignedGroupZeroCount_sum]
  exact Equiv.sum_comp σ (fun i => if (u i).2 = 0 then (1 : ℕ) else 0)

theorem giantSignedPendingZeros_permute {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (m : GiantSignedMemory P) (σ : (j : J) → Equiv.Perm (Fin (m.1 j))) :
    giantSignedPendingZeros (giantSignedMemoryPermute m σ) = giantSignedPendingZeros m := by
  classical
  change (∑ j, giantSignedGroupZeroCount (m.2 j ∘ σ j)) =
    ∑ j, giantSignedGroupZeroCount (m.2 j)
  exact Finset.sum_congr rfl (fun j _ => giantSignedGroupZeroCount_permute (m.2 j) (σ j))

theorem giantSignedPendingDamping_permute {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (ρ : ℝ) (m : GiantSignedMemory P) (σ : (j : J) → Equiv.Perm (Fin (m.1 j))) :
    giantSignedPendingDamping ρ (giantSignedMemoryPermute m σ) =
      giantSignedPendingDamping ρ m := by
  unfold giantSignedPendingDamping
  rw [giantSignedPendingZeros_permute]

private theorem giantSignedMemory_append_cast {J : Type*} {P : J → Finset ℕ}
    {k n a : J → ℕ} (h : ∀ j, k j = n j)
    (u : (j : J) → Fin (k j) → GiantSignedParticle (P j))
    (p : (j : J) → Fin (a j) → GiantSignedParticle (P j)) :
    (⟨fun j => k j + a j, fun j => Fin.append (u j) (p j)⟩ : GiantSignedMemory P) =
      ⟨fun j => n j + a j,
        fun j => Fin.append (fun i => u j (Fin.cast (h j).symm i)) (p j)⟩ := by
  have he : k = n := funext h
  subst n
  rfl

def giantSignedEdgeInput {J : Type*} {P : J → Finset ℕ} {n a : J → ℕ}
    (d : ℤ) (u : (j : J) → Fin (n j) → GiantSignedParticle (P j))
    (p : (j : J) → Fin (a j) → P j) : GiantSignedMemory P :=
  ⟨fun j => n j + a j, fun j => Fin.append (u j) (fun i => giantSignedParticleAt (-d) (p j i))⟩

def giantSignedEdgeOutput {J : Type*} {P : J → Finset ℕ} {n b : J → ℕ}
    (d : ℤ) (u : (j : J) → Fin (n j) → GiantSignedParticle (P j))
    (s : (j : J) → Fin (b j) → P j) : GiantSignedMemory P :=
  ⟨fun j => n j + b j, fun j => Fin.append
    (fun i => giantSignedParticleTranslate d (u j i))
    (fun i => giantSignedParticleAt d (s j i))⟩

theorem giantSignedEdgeTarget_eq_output {J : Type*} {P : J → Finset ℕ}
    {t n : J → ℕ} (d : ℤ) (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (n j + (T j).card))
    (source : (j : J) → Fin (t j) → P j)
    (old : (j : J) → Fin (n j + (T j).card) → GiantSignedParticle (P j)) :
    giantSignedEdgeTarget d ⟨fun j => n j + (T j).card, old⟩ source ⟨S, T, e⟩ =
      giantSignedEdgeOutput d (fun j => giantSignedRetrievalSurvivors (e j) (old j))
        (fun j => giantSignedEdgeSelected (S j) (source j)) := by
  let h (j : J) : ((Finset.univ.map (e j))ᶜ).card = n j := by
    simp only [Finset.card_compl, Fintype.card_fin, Finset.card_map, Finset.card_univ]
    omega
  exact giantSignedMemory_append_cast h
    (fun j i => giantSignedParticleTranslate d
      ((markedRawSubsetTupleEquiv (Finset.univ.map (e j)) (old j)).2 i))
    (fun j i => giantSignedParticleAt d (giantSignedEdgeSelected (S j) (source j) i))

theorem giantSignedEdgeInput_reverse {J : Type*} {P : J → Finset ℕ} {n b : J → ℕ}
    (d : ℤ) (u : (j : J) → Fin (n j) → GiantSignedParticle (P j))
    (s : (j : J) → Fin (b j) → P j) :
    giantSignedEdgeInput (-d) (giantSignedTupleTranslate d n u) s =
      giantSignedEdgeOutput d u s := by
  simp only [giantSignedEdgeInput, giantSignedEdgeOutput, neg_neg]
  rfl

theorem giantSignedEdgeOutput_reverse {J : Type*} {P : J → Finset ℕ} {n a : J → ℕ}
    (d : ℤ) (u : (j : J) → Fin (n j) → GiantSignedParticle (P j))
    (p : (j : J) → Fin (a j) → P j) :
    giantSignedEdgeOutput (-d) (giantSignedTupleTranslate d n u) p =
      giantSignedEdgeInput d u p := by
  unfold giantSignedEdgeOutput giantSignedEdgeInput
  apply congrArg (fun f : (j : J) → Fin (n j + a j) → GiantSignedParticle (P j) =>
    (⟨fun j => n j + a j, f⟩ : GiantSignedMemory P))
  funext j
  apply congrArg₂ Fin.append
  · funext i
    exact giantSignedParticleTranslate_neg d (u j i)
  · rfl

def giantSignedEdgePendingFactor {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {n a b : J → ℕ} (ρ : ℝ) (d : ℤ)
    (u : (j : J) → Fin (n j) → GiantSignedParticle (P j))
    (p : (j : J) → Fin (a j) → P j) (s : (j : J) → Fin (b j) → P j) : ℂ :=
  (giantSignedPendingDamping ρ (giantSignedEdgeInput d u p) : ℂ) *
    (giantSignedPendingDamping ρ (giantSignedEdgeOutput d u s) : ℂ)

theorem giantSignedEdgePendingFactor_reverse {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {n a b : J → ℕ} (ρ : ℝ) (d : ℤ)
    (u : (j : J) → Fin (n j) → GiantSignedParticle (P j))
    (p : (j : J) → Fin (a j) → P j) (s : (j : J) → Fin (b j) → P j) :
    giantSignedEdgePendingFactor ρ (-d) (giantSignedTupleTranslate d n u) s p =
      giantSignedEdgePendingFactor ρ d u p s := by
  rw [giantSignedEdgePendingFactor, giantSignedEdgeInput_reverse,
    giantSignedEdgeOutput_reverse, giantSignedEdgePendingFactor, mul_comm]

end
end ArtinMatthews
