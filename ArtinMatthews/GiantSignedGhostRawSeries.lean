module

public import ArtinMatthews.GiantSignedGhostRawPairing
public import ArtinMatthews.GiantSignedGhostGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual infinite birth row is exactly the sum of its raw degree
blocks. All interchanges here are justified on exponential tests. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

theorem giantSignedGhostRawPairingBlock_birth (ν : P → ℝ) (A C D : ℂ)
    (f h : GiantSignedGroupMemory P → ℂ) (k b : ℕ) (S : Finset (Fin k)) :
    giantSignedGhostRawPairingBlock ν A C D f h ⟨k, S, b⟩ =
      ∑ a : Fin k → GiantSignedParticle P,
        (giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩) *
          (if S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩ then
            D ^ S.card * A ^ ((giantSignedGhostZeroIndices ⟨k, a⟩).card - S.card) *
              giantSignedGhostBirthContribution ν C ⟨k, a⟩ S h b else 0) := by
  classical
  unfold giantSignedGhostRawPairingBlock
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩
  · simp only [hz, ite_true, giantSignedGhostBirthContribution]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    ring
  · simp only [hz, ite_false, Finset.sum_const_zero, mul_zero]

theorem giantSignedGhostRawPairingBlock_birth_summable (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ) (f h : GiantSignedGroupMemory P → ℂ)
    (B v : ℝ) (hh : ∀ m, ‖h m‖ ≤ B * v ^ m.1) (k : ℕ) (S : Finset (Fin k)) :
    Summable (fun b : ℕ => giantSignedGhostRawPairingBlock ν A C D f h ⟨k, S, b⟩) := by
  classical
  simp_rw [giantSignedGhostRawPairingBlock_birth]
  apply summable_sum
  intro a _
  by_cases hz : S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩
  · simp only [hz, ite_true]
    simpa only [mul_assoc] using
      (giantSignedGhostBirthContribution_summable ν hν C ⟨k, a⟩ S h B v hh).mul_left
        ((giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩) *
          (D ^ S.card * A ^ ((giantSignedGhostZeroIndices ⟨k, a⟩).card - S.card)))
  · simp only [hz, ite_false, mul_zero]
    exact summable_zero

theorem giantSignedGhostRawPairingBlock_tsum_birth (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ) (f h : GiantSignedGroupMemory P → ℂ)
    (B v : ℝ) (hh : ∀ m, ‖h m‖ ≤ B * v ^ m.1) (k : ℕ) (S : Finset (Fin k)) :
    (∑' b : ℕ, giantSignedGhostRawPairingBlock ν A C D f h ⟨k, S, b⟩) =
      ∑ a : Fin k → GiantSignedParticle P,
        (giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩) *
          (if S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩ then
            D ^ S.card * A ^ ((giantSignedGhostZeroIndices ⟨k, a⟩).card - S.card) *
              ∑' b, giantSignedGhostBirthContribution ν C ⟨k, a⟩ S h b else 0) := by
  classical
  simp_rw [giantSignedGhostRawPairingBlock_birth]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases hz : S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩
    · simp only [hz, ite_true, tsum_mul_left]
    · simp only [hz, ite_false, mul_zero, tsum_zero]
  · intro a _
    by_cases hz : S ⊆ giantSignedGhostZeroIndices ⟨k, a⟩
    · simp only [hz, ite_true]
      simpa only [mul_assoc] using
        (giantSignedGhostBirthContribution_summable ν hν C ⟨k, a⟩ S h B v hh).mul_left
          ((giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩) *
            (D ^ S.card * A ^ ((giantSignedGhostZeroIndices ⟨k, a⟩).card - S.card)))
    · simp only [hz, ite_false, mul_zero]
      exact summable_zero

theorem giantSignedGhost_subset_sum {α E : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid E] (Z : Finset α) (F : Finset α → E) :
    (∑ S : Finset α, if S ⊆ Z then F S else 0) = ∑ S ∈ Z.powerset, F S := by
  classical
  have hs : (Finset.univ : Finset (Finset α)).filter (fun S => S ⊆ Z) = Z.powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  rw [← Finset.sum_filter, hs]

theorem giantSignedGhostRawPairingBlock_source_degree (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ) (f h : GiantSignedGroupMemory P → ℂ)
    (B v : ℝ) (hh : ∀ m, ‖h m‖ ≤ B * v ^ m.1) (k : ℕ) :
    (∑ S : Finset (Fin k), ∑' b : ℕ,
      giantSignedGhostRawPairingBlock ν A C D f h ⟨k, S, b⟩) =
      ∑ a : Fin k → GiantSignedParticle P,
        (giantSignedGroupMemoryMass ν ⟨k, a⟩ : ℂ) * star (f ⟨k, a⟩) *
          giantSignedGhostGroupApply ν A C D h ⟨k, a⟩ := by
  classical
  simp_rw [giantSignedGhostRawPairingBlock_tsum_birth ν hν A C D f h B v hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, giantSignedGhost_subset_sum]
  rfl

end
end ArtinMatthews
