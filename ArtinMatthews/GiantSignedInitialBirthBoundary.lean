module

public import ArtinMatthews.GiantSignedProjectedBoundaryEnergy
public import ArtinMatthews.GiantSignedEnergyDomination


set_option backward.privateInPublic true
@[expose] public section

/-! The phase at the initial performed births multiplies the original
Haar and tilted active boundary sum. Its energy costs no extra factor. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedInitialBirthBoundary (φ : MarkedPhysicalMarking PB M → ℂ)
    (s : GiantSignedState PS PB M) : ℂ :=
  giantSignedBoundary s * star (φ s.2.1)

theorem giantSignedInitialBirthBoundary_pairing (ν : ∀ g, PB g → ℝ)
    (φ : MarkedPhysicalMarking PB M → ℂ) (w : GiantSignedState PS PB M → ℂ) :
    giantSignedStatePairing PS ν (giantSignedInitialBirthBoundary PS φ) w =
      ∑ y : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
        ((giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a : ℝ) : ℂ) *
          φ a * w (y,a,giantSignedEmptyMemory PB) := by
  rw [giantSignedStatePairing, tsum_eq_single (giantSignedEmptyMemory PB)]
  · simp only [giantSignedStateFiberPairing, Fintype.sum_prod_type, giantSignedStateMass,
      giantSignedEmptyMemory_mass, giantSignedInitialBirthBoundary, giantSignedBoundary_empty,
      mul_one, one_mul, star_star]
  · intro m hm
    simp only [giantSignedStateFiberPairing, giantSignedInitialBirthBoundary,
      giantSignedBoundary, hm, ite_false, zero_mul, star_zero, mul_zero, Finset.sum_const_zero]

theorem giantSignedInitialBirthBoundary_energy_le
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (φ : MarkedPhysicalMarking PB M → ℂ) (hφ : ∀ a, ‖φ a‖ ≤ 1) :
    giantSignedStateEnergy PS ν (giantSignedInitialBirthBoundary PS φ) ≤
      giantSignedStateEnergy PS ν (giantSignedBoundary (M := M)) := by
  have h := giantSignedStateEnergy_norm_domination PS hVS ν hν
    (giantSignedInitialBirthBoundary PS φ) giantSignedBoundary 1 (fun s => by
      rw [giantSignedInitialBirthBoundary, norm_mul, norm_star, one_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hφ s.2.1))
  simpa only [one_pow, ENNReal.ofReal_one, one_mul] using h

theorem giantSignedInitialBirthBoundary_norm_of_energy
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (φ : MarkedPhysicalMarking PB M → ℂ) (hφ : ∀ a, ‖φ a‖ ≤ 1)
    (w : GiantSignedState PS PB M → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hb : giantSignedStateEnergy PS ν (giantSignedBoundary (M := M)) ≤ 2)
    (hw : giantSignedStateEnergy PS ν w ≤
      ENNReal.ofReal (C^2) * giantSignedStateEnergy PS ν (giantSignedBoundary (M := M))) :
    ‖∑ y : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
      ((giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a : ℝ) : ℂ) *
        φ a * w (y,a,giantSignedEmptyMemory PB)‖ ≤ 2*C := by
  have hp := (giantSignedInitialBirthBoundary_energy_le PS hVS ν hν φ hφ).trans hb
  have hw' : giantSignedStateEnergy PS ν w ≤ ENNReal.ofReal (C^2) * 2 :=
    hw.trans (mul_le_mul_right hb _)
  have hfinP := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp
  have hfinW := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofNat_ne_top) hw'
  have h := giantSignedStatePairing_energy PS hVS ν hν
    (giantSignedInitialBirthBoundary PS φ) w hfinP hfinW
  rw [← giantSignedInitialBirthBoundary_pairing PS ν φ w]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hC)).mp
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp
  calc
    _ ≤ _ := h
    _ ≤ 2 * (ENNReal.ofReal (C^2) * 2) := mul_le_mul' hp hw'
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (sq_nonneg C),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end
end ArtinMatthews
