module

public import ArtinMatthews.GiantSignedProjectedBoundaryEnergy
public import ArtinMatthews.GiantSignedSourceContractionBudget
public import ArtinMatthews.GiantSignedSourceOmissionGain


set_option backward.privateInPublic true
@[expose] public section

/-! The exact local signed edge estimates feed the original projected
boundary pairing with its stated source exponent. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedSourceProjectedBoundaryPairing_norm_of_local
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (q ρ θ L Cv G E : ℝ) (hL : 2 ≤ L) (hgap : E + Cv/2 + 3 ≤ G)
    (n : ℕ) (hn : 1 ≤ n) (hCv : Cv ≤ (n : ℝ))
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (hboundary : giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2) :
    let N := giantSignedSourceMemoryLimit L
    let V : B → ℝ := fun g => bandReciprocalMass (PB g)
    (∀ (i : Fin (n+1)) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedVisit N ν V (giantSignedSourceVisitQ q n i) ρ w) ≤
        ENNReal.ofReal (L ^ Cv) * giantSignedStateEnergy PS ν w) →
    (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply N ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (fun _ _ _ => 1) w) ≤
        ENNReal.ofReal ((L ^ (-G)) ^ (2 : ℕ)) * giantSignedStateEnergy PS ν w) →
    ‖giantSignedProjectedChronologicalBoundaryPairing (PS := PS) N ν V q ρ θ
      n patterns C κ (giantSignedSourceVisitQ q n) ζ K (fun _ _ _ _ => 1)‖ ≤
      (L ^ (-E)) ^ n := by
  dsimp only
  intro hvisit hedge
  let N := giantSignedSourceMemoryLimit L
  let V : B → ℝ := fun g => bandReciprocalMass (PB g)
  let w := giantSignedProjectedChronologicalBoundaryPairing (PS := PS) N ν V q ρ θ
    n patterns C κ (giantSignedSourceVisitQ q n) ζ K (fun _ _ _ _ => 1)
  have h := giantSignedProjectedBoundaryPairing_energy_of_local PS N ν hν hVS V
    q ρ θ (L ^ Cv) ((L ^ (-G)) ^ (2 : ℕ)) n patterns C κ
    (giantSignedSourceVisitQ q n) ζ K hboundary hvisit hedge
  have hL0 : 0 ≤ L := by linarith
  have hC0 : 0 ≤ L ^ Cv := Real.rpow_nonneg hL0 _
  have hE0 : 0 ≤ L ^ (-E) := Real.rpow_nonneg hL0 _
  have hreal : ‖w‖ ^ 2 ≤ (L ^ (-E)) ^ (2*n) := by
    apply (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hE0 _)).mp
    refine h.trans ?_
    rw [← ENNReal.ofReal_pow hC0, ← ENNReal.ofReal_pow (sq_nonneg (L ^ (-G)))]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (pow_nonneg hC0 _))]
    exact ENNReal.ofReal_le_ofReal (giantSignedSourceWord_contraction_budget hL hn hCv hgap)
  rw [Nat.mul_comm 2 n, pow_mul] at hreal
  exact (sq_le_sq₀ (norm_nonneg w) (pow_nonneg hE0 _)).mp hreal

end
end ArtinMatthews
