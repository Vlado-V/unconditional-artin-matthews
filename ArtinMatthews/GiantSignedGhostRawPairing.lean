module

public import ArtinMatthews.GiantSignedFockMoments
public import ArtinMatthews.GiantSignedGhostCountableDegrees


set_option backward.privateInPublic true
@[expose] public section

/-! The all-degree pairing is assembled from actual indexed deletion
and birth blocks. Its finite-degree form has the original factorial. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

omit [∀ p : P, NeZero p.val] in
theorem giantSignedGhostTarget_cast {k n b : ℕ}
    (a : Fin k → GiantSignedParticle P) (S : Finset (Fin k))
    (hn : Sᶜ.card = n) (β : Fin b → P) :
    giantSignedGhostTarget ⟨k, a⟩ S β =
      ⟨n + b, Fin.append (markedRawSurvivorTupleCast S hn a) (giantSignedZeroTuple β)⟩ := by
  cases hn
  rfl

omit [∀ p : P, NeZero p.val] in
theorem giantSignedGhost_deleted_zero_cast_iff {k t : ℕ}
    (a : Fin k → GiantSignedParticle P) (S : Finset (Fin k)) (ht : S.card = t) :
    (∀ i, (markedRawDeletedTupleCast S ht a i).2 = 0) ↔
      S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩ := by
  cases ht
  exact giantSignedGhost_deleted_zero_iff a S

def giantSignedGhostRawPairingBlock (ν : P → ℝ) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (r : GiantSignedGhostRawShape) : ℂ :=
  ∑ a : Fin r.1 → GiantSignedParticle P, ∑ β : Fin r.2.2 → P,
    if r.2.1 ⊆ giantSignedGhostZeroIndices ⟨r.1, a⟩ then
      (giantSignedGroupMemoryMass ν ⟨r.1, a⟩ : ℂ) * star (f ⟨r.1, a⟩) *
        D ^ r.2.1.card * A ^ ((giantSignedGhostZeroIndices ⟨r.1, a⟩).card - r.2.1.card) *
        (C ^ r.2.2 / (Nat.factorial r.2.2 : ℂ)) *
        (∏ i, (ν (β i) : ℂ)) * h (giantSignedGhostTarget ⟨r.1, a⟩ r.2.1 β)
    else 0

theorem giantSignedGhostRawPairingBlock_degree (ν : P → ℝ) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (n t b : ℕ) :
    (∑ S : MarkedRawDeletionBatch (n + t) t,
      giantSignedGhostRawPairingBlock ν A C D f h ⟨n + t, S.val, b⟩) =
      giantSignedGhostDegreePairing ν A C D n t b
        (fun a => f ⟨n + t, a⟩) (fun a => h ⟨n + b, a⟩) := by
  classical
  rw [giantSignedGhostDegreePairing_original]
  unfold giantSignedGhostRawPairingBlock
  dsimp only
  change (∑ S : MarkedRawDeletionBatch (n + t) t,
    ∑ a : Fin (n + t) → GiantSignedParticle P, ∑ β : Fin b → P,
      if S.val ⊆ giantSignedGhostZeroIndices ⟨n + t, a⟩ then
        (giantSignedGroupMemoryMass ν ⟨n + t, a⟩ : ℂ) * star (f ⟨n + t, a⟩) *
          D ^ S.val.card * A ^ ((giantSignedGhostZeroIndices ⟨n + t, a⟩).card - S.val.card) *
          (C ^ b / (Nat.factorial b : ℂ)) * (∏ i, (ν (β i) : ℂ)) *
          h (giantSignedGhostTarget ⟨n + t, a⟩ S.val β)
      else 0) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have ht := markedRawDeletionBatch_deleted_card S
  have hn := markedRawDeletionBatch_survivor_card rfl S
  simp only [giantSignedGhost_deleted_zero_cast_iff a S.val ht]
  by_cases hz : S.val ⊆ giantSignedGhostZeroIndices ⟨n + t, a⟩
  · simp only [hz, ite_true, giantSignedGhostTarget_cast a S.val hn]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    simp only [giantSignedGroupMemoryMass, Complex.ofReal_div, Complex.ofReal_prod,
      Complex.ofReal_natCast, ht, giantSignedGroupZeroCount]
    ring
  · simp only [hz, ite_false, Finset.sum_const_zero, mul_zero]

def giantSignedGhostPositivePairingBlock (ν : P → ℝ) (A C D : ℝ)
    (f h : GiantSignedGroupMemory P → ℝ) (r : GiantSignedGhostRawShape) : ℝ :=
  ∑ a : Fin r.1 → GiantSignedParticle P, ∑ β : Fin r.2.2 → P,
    if r.2.1 ⊆ giantSignedGhostZeroIndices ⟨r.1, a⟩ then
      giantSignedGroupMemoryMass ν ⟨r.1, a⟩ * f ⟨r.1, a⟩ *
        D ^ r.2.1.card * A ^ ((giantSignedGhostZeroIndices ⟨r.1, a⟩).card - r.2.1.card) *
        (C ^ r.2.2 / (Nat.factorial r.2.2 : ℝ)) *
        (∏ i, ν (β i)) * h (giantSignedGhostTarget ⟨r.1, a⟩ r.2.1 β)
    else 0

theorem giantSignedGhostPositivePairingBlock_coe (ν : P → ℝ) (A C D : ℝ)
    (f h : GiantSignedGroupMemory P → ℝ) (r : GiantSignedGhostRawShape) :
    (giantSignedGhostPositivePairingBlock ν A C D f h r : ℂ) =
      giantSignedGhostRawPairingBlock ν (A : ℂ) (C : ℂ) (D : ℂ)
        (fun m => (f m : ℂ)) (fun m => (h m : ℂ)) r := by
  classical
  unfold giantSignedGhostPositivePairingBlock giantSignedGhostRawPairingBlock
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro β _
  split_ifs <;> push_cast <;> simp only [Complex.star_def, Complex.conj_ofReal]

theorem giantSignedGhostPositivePairingBlock_nonneg (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (f h : GiantSignedGroupMemory P → ℝ) (hf : ∀ m, 0 ≤ f m) (hh : ∀ m, 0 ≤ h m)
    (r : GiantSignedGhostRawShape) :
    0 ≤ giantSignedGhostPositivePairingBlock ν A C D f h r := by
  unfold giantSignedGhostPositivePairingBlock
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro β _
  split_ifs
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν _) (hf _))
              (pow_nonneg hD _)) (pow_nonneg hA _))
          (div_nonneg (pow_nonneg hC _) (Nat.cast_nonneg _)))
        (Finset.prod_nonneg fun i _ => hν (β i))) (hh _)
  · exact le_rfl

theorem giantSignedGhostRawPairingBlock_norm_le (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (r : GiantSignedGhostRawShape) :
    ‖giantSignedGhostRawPairingBlock ν A C D f h r‖ ≤
      giantSignedGhostPositivePairingBlock ν ‖A‖ ‖C‖ ‖D‖
        (fun m => ‖f m‖) (fun m => ‖h m‖) r := by
  classical
  unfold giantSignedGhostRawPairingBlock giantSignedGhostPositivePairingBlock
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro β _
  split_ifs
  · simp only [norm_mul, norm_pow, norm_div, Complex.norm_natCast, norm_star,
      Complex.norm_real, Real.norm_of_nonneg (giantSignedGroupMemoryMass_nonneg ν hν _), norm_prod]
    have hp : (∏ i, ‖ν (β i)‖) = ∏ i, ν (β i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact Real.norm_of_nonneg (hν (β i))
    rw [hp]
  · simp only [norm_zero, le_refl]

end
end ArtinMatthews
