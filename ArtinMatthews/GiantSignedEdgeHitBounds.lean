module

public import ArtinMatthews.GiantSignedEdgeStorePromote


set_option backward.privateInPublic true
@[expose] public section

/-! Literal translated hit sets control the outgoing damping. All stored
particles and both source and target degrees are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedParticle_eq_at_zero_iff {P : Finset ℕ}
    (x : GiantSignedParticle P) (p : P) :
    x = giantSignedParticleAt 0 p ↔ x.1 = p ∧ x.2 = 0 := by
  rcases x with ⟨q, r⟩
  constructor
  · intro h
    cases h
    simp only [Int.cast_zero, and_self]
  · rintro ⟨h, hr⟩
    subst p
    simpa only [giantSignedParticleAt, Int.cast_zero] using congrArg (Sigma.mk q) hr

def giantSignedEdgeHitIndices {J : Type*} {P : J → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (j : J) : Finset (Fin (m.1 j)) := by
  classical
  exact Finset.univ.filter (fun i => (giantSignedParticleTranslate d (m.2 j i)).2 = 0)

theorem giantSignedEdgeHitIndices_mem {J : Type*} {P : J → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (j : J) (i : Fin (m.1 j)) :
    i ∈ giantSignedEdgeHitIndices d m j ↔
      (giantSignedParticleTranslate d (m.2 j i)).2 = 0 := by
  classical
  simp only [giantSignedEdgeHitIndices, Finset.mem_filter, Finset.mem_univ, true_and]

def giantSignedEdgePromotionPrimes {J : Type*} {P : J → Finset ℕ} {a : J → ℕ}
    (m : GiantSignedMemory P) (e : (j : J) → Fin (a j) ↪ Fin (m.1 j)) :
    GiantSignedPrimeTuple P a := fun j i => (m.2 j (e j i)).1

theorem giantSignedEdgeHits_indices_labels {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (target : GiantSignedPrimeTuple P t)
    (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    GiantSignedEdgeHits d m target ⟨S, T, e⟩ ↔
      (∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j) ∧
      (∀ j, giantSignedEdgeSelected (T j) (target j) =
        giantSignedEdgePromotionPrimes m e j) := by
  constructor
  · intro h
    constructor
    · intro j i
      rw [giantSignedEdgeHitIndices_mem]
      exact ((giantSignedParticle_eq_at_zero_iff _ _).mp (h j i)).2
    · intro j
      funext i
      exact ((giantSignedParticle_eq_at_zero_iff _ _).mp (h j i)).1.symm
  · rintro ⟨h, hp⟩ j i
    apply (giantSignedParticle_eq_at_zero_iff _ _).mpr
    exact ⟨(congrFun (hp j) i).symm,
      (giantSignedEdgeHitIndices_mem d m j (e j i)).mp (h j i)⟩

theorem giantSignedGroupZeroCount_append {P : Finset ℕ} {n a : ℕ}
    (u : Fin n → GiantSignedParticle P) (v : Fin a → GiantSignedParticle P) :
    giantSignedGroupZeroCount (Fin.append u v) =
      giantSignedGroupZeroCount u + giantSignedGroupZeroCount v := by
  classical
  rw [giantSignedGroupZeroCount_sum, Fin.sum_univ_add,
    giantSignedGroupZeroCount_sum, giantSignedGroupZeroCount_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun p : GiantSignedParticle P => if p.2 = 0 then (1 : ℕ) else 0)
      (Fin.append_left u v i)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun p : GiantSignedParticle P => if p.2 = 0 then (1 : ℕ) else 0)
      (Fin.append_right u v i)

theorem giantSignedEdgeTarget_zeros_ge {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : GiantSignedPrimeTuple P t)
    (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j))
    (h : ∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j) (j : J) :
    (giantSignedEdgeHitIndices d m j).card - (T j).card ≤
      giantSignedGroupZeroCount ((giantSignedEdgeTarget d m source ⟨S, T, e⟩).2 j) := by
  classical
  let R : Finset (Fin (m.1 j)) := Finset.univ.map (e j)
  let u : Fin (m.1 j) → GiantSignedParticle (P j) :=
    fun i => giantSignedParticleTranslate d (m.2 j i)
  have hR : R ⊆ giantSignedGhostZeroIndices ⟨m.1 j, u⟩ := by
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨k, _, rfl⟩
    change e j k ∈ Finset.univ.filter (fun i => (u i).2 = 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (giantSignedEdgeHitIndices_mem d m j (e j k)).mp (h j k)⟩
  have hs := giantSignedGhost_survivor_zero_count u R hR
  have hc : R.card = (T j).card := by
    simp only [R, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hu : giantSignedGroupZeroCount u = (giantSignedEdgeHitIndices d m j).card := rfl
  change _ ≤ giantSignedGroupZeroCount
    (Fin.append ((markedRawSubsetTupleEquiv R u).2)
      (fun i => giantSignedParticleAt d (giantSignedEdgeSelected (S j) (source j) i)))
  rw [giantSignedGroupZeroCount_append, hs, hu, hc]
  exact Nat.le_add_right _ _

theorem giantSignedEdgeTarget_damping_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {t : J → ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (d : ℤ) (m : GiantSignedMemory P) (source : GiantSignedPrimeTuple P t)
    (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j))
    (h : ∀ j i, e j i ∈ giantSignedEdgeHitIndices d m j) :
    giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) ≤
      ∏ j, ρ ^ ((giantSignedEdgeHitIndices d m j).card - (T j).card) := by
  classical
  have hz : (∑ j, ((giantSignedEdgeHitIndices d m j).card - (T j).card)) ≤
      giantSignedPendingZeros (giantSignedEdgeTarget d m source ⟨S, T, e⟩) :=
    Finset.sum_le_sum (fun j _ => giantSignedEdgeTarget_zeros_ge d m source S T e h j)
  rw [Finset.prod_pow_eq_pow_sum]
  exact pow_le_pow_of_le_one hρ hρ1 hz

theorem giantSignedEdgeTarget_degree_gauge {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {t : J → ℕ} {v : ℝ} (hv : 1 ≤ v)
    (d : ℤ) (m : GiantSignedMemory P) (source : GiantSignedPrimeTuple P t)
    (S T : (j : J) → Finset (Fin (t j)))
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    v ^ (∑ j, (giantSignedEdgeTarget d m source ⟨S, T, e⟩).1 j) ≤
      v ^ (∑ j, m.1 j) * ∏ j, v ^ (S j).card := by
  classical
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← Finset.sum_add_distrib]
  apply pow_le_pow_right₀ hv
  apply Finset.sum_le_sum
  intro j _
  rw [giantSignedEdgeTarget_degree]
  exact Nat.add_le_add_right (Nat.sub_le _ _) _

end
end ArtinMatthews
