module

public import ArtinMatthews.GiantSignedStatePermutationEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The original memory-size projection acts on the full signed state carrier. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

def giantSignedStateMemoryCutoff (N : ℕ) (f : GiantSignedState PS PB M → ℂ)
    (s : GiantSignedState PS PB M) : ℂ :=
  if (∑ g, s.2.2.1 g) ≤ N then f s else 0

theorem giantSignedStateMemoryCutoff_of_le (N : ℕ) (f : GiantSignedState PS PB M → ℂ)
    (s : GiantSignedState PS PB M) (hs : (∑ g, s.2.2.1 g) ≤ N) :
    giantSignedStateMemoryCutoff N f s = f s := by
  exact ite_eq_left hs

theorem giantSignedStateMemoryCutoff_of_lt (N : ℕ) (f : GiantSignedState PS PB M → ℂ)
    (s : GiantSignedState PS PB M) (hs : N < ∑ g, s.2.2.1 g) :
    giantSignedStateMemoryCutoff N f s = 0 := by
  exact ite_eq_right (not_le_of_gt hs)

theorem giantSignedStateMemoryCutoff_idempotent (N : ℕ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateMemoryCutoff N (giantSignedStateMemoryCutoff N f) =
      giantSignedStateMemoryCutoff N f := by
  funext s
  unfold giantSignedStateMemoryCutoff
  split_ifs <;> rfl

theorem giantSignedStateMemoryCutoff_add (N : ℕ) (f g : GiantSignedState PS PB M → ℂ) :
    giantSignedStateMemoryCutoff N (f + g) =
      giantSignedStateMemoryCutoff N f + giantSignedStateMemoryCutoff N g := by
  funext s
  by_cases h : (∑ g, s.2.2.1 g) ≤ N <;> simp [giantSignedStateMemoryCutoff, h]

theorem giantSignedStateMemoryCutoff_smul (N : ℕ) (a : ℂ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateMemoryCutoff N (a • f) = a • giantSignedStateMemoryCutoff N f := by
  funext s
  by_cases h : (∑ g, s.2.2.1 g) ≤ N <;> simp [giantSignedStateMemoryCutoff, h]

theorem giantSignedStateMemoryCutoff_norm_le (N : ℕ) (f : GiantSignedState PS PB M → ℂ)
    (s : GiantSignedState PS PB M) :
    ‖giantSignedStateMemoryCutoff N f s‖ ≤ ‖f s‖ := by
  unfold giantSignedStateMemoryCutoff
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, norm_nonneg]

variable [DecidableEq S] [DecidableEq B]
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStateMemoryCutoff_energy_le
    (ν : ∀ g, PB g → ℝ) (N : ℕ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N f) ≤ giantSignedStateEnergy PS ν f := by
  rw [giantSignedStateEnergy_eq_tsum, giantSignedStateEnergy_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro s
  unfold giantSignedStateMemoryCutoff
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, ENNReal.ofReal_zero,
      zero_le]

omit [DecidableEq S] [DecidableEq B]
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedStateMemoryCutoff_slot_permute
    (N : ℕ) (f : GiantSignedState PS PB M → ℂ)
    (πS : S → Equiv.Perm (Fin M)) (πB : B → Equiv.Perm (Fin M)) :
    giantSignedStateMemoryCutoff N (fun s => f (giantSignedStatePermute PS πS πB s)) =
      fun s => giantSignedStateMemoryCutoff N f (giantSignedStatePermute PS πS πB s) := by
  rfl

omit [DecidableEq S] [DecidableEq B]
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedStateMemoryCutoff_memory_symmetric
    (N : ℕ) (f : GiantSignedState PS PB M → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric (fun m => giantSignedStateMemoryCutoff N f (s,a,m)) := by
  intro s a m σ
  change (if (∑ g, m.1 g) ≤ N then f (s,a,giantSignedMemoryPermute m σ) else 0) =
    if (∑ g, m.1 g) ≤ N then f (s,a,m) else 0
  by_cases h : (∑ g, m.1 g) ≤ N
  · rw [ite_eq_left h, ite_eq_left h]
    exact hf s a m σ
  · rw [ite_eq_right h, ite_eq_right h]

end
end ArtinMatthews
