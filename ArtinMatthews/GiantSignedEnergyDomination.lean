module

public import ArtinMatthews.GiantSignedStatePermutationEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise norm domination preserves the exact original state energy. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStateEnergy_norm_domination
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (F G : GiantSignedState PS PB M → ℂ) (A : ℝ)
    (hFG : ∀ s, ‖F s‖ ≤ A * ‖G s‖) :
    giantSignedStateEnergy PS ν F ≤ ENNReal.ofReal (A ^ 2) * giantSignedStateEnergy PS ν G := by
  have hstate (s : GiantSignedState PS PB M) : 0 ≤ giantSignedStateMass PS ν s := by
    apply mul_nonneg
    · apply mul_nonneg
      · unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
        exact div_nonneg
          (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
          (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g _))
    · exact giantSignedMemoryMass_nonneg ν hν s.2.2
  rw [giantSignedStateEnergy_eq_tsum, giantSignedStateEnergy_eq_tsum, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hFG s) 2
  rw [mul_pow] at hs
  calc
    _ ≤ ENNReal.ofReal (giantSignedStateMass PS ν s * (A ^ 2 * ‖G s‖ ^ 2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (hstate s))
    _ = _ := by
      rw [mul_left_comm, ENNReal.ofReal_mul (sq_nonneg A)]

end
end ArtinMatthews
