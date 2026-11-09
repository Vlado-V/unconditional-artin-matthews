module

public import ArtinMatthews.GiantTwoSidedPhysicalAbsolutePairing
public import ArtinMatthews.PrimeExtractionMellinBilinear


set_option backward.privateInPublic true
@[expose] public section

/-! The literal reciprocal position cost is the same absolute form
with the normalized left Mellin multiplier and the exterior factor 1/X. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPhysicalFamilyAbsolutePairing_reciprocal_eq
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) {Z : Finset ℕ}
    {X : ℝ} (hX : 0 < X) (v : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    (∑ c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell,
      ∑ s : GiantTwoSidedEndpointState P (k+ell) Z, ∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
        ‖(markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) *
          (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ) *
          giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t / (s.val.1.val : ℂ) *
          star (f s.val.1.val) * g t‖) =
      X⁻¹ * giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K
        (fun n => ((X/(n : ℝ) : ℝ) : ℂ) * primeExtractionMellinPhase (-v) n * f n) g := by
  unfold giantTwoSidedPhysicalFamilyAbsolutePairing
  simp only [mul_sum]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro t _
  let n := s.val.1.val
  let a : ℂ := (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) *
    (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ) *
    giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t
  change ‖a / (n : ℂ) * star (f n) * g t‖ =
    X⁻¹ * ‖a * star (((X/(n : ℝ) : ℝ) : ℂ) * primeExtractionMellinPhase (-v) n * f n) * g t‖
  have hratio : 0 ≤ X / (n : ℝ) := div_nonneg hX.le (Nat.cast_nonneg _)
  simp only [norm_mul, norm_div, norm_star, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg hratio, primeExtractionMellinPhase_norm, mul_one]
  have hc : X⁻¹ * (X / (n : ℝ)) = (n : ℝ)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
  calc
    _ = (n : ℝ)⁻¹ * (‖a‖ * ‖f n‖ * ‖g t‖) := by ring
    _ = _ := by rw [← hc]; ring

end
end ArtinMatthews
