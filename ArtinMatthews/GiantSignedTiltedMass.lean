module

public import ArtinMatthews.GiantSignedTiltBandBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual tilted prime law has its derived total mass. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedTiltedPrimeLaw_sum_bounds (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ)
    (hV : 0 < bandReciprocalMass P) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ p : P, Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin < 1) :
    1 ≤ ∑ p : P, giantSignedTiltedPrimeLaw P q p ∧
      (∑ p : P, giantSignedTiltedPrimeLaw P q p) ≤ (1 - (n : ℝ) / Pmin)⁻¹ := by
  classical
  constructor
  · calc
      1 = ∑ p : P, markedHarmonicAtom P p := (markedHarmonicAtom_sum P hV).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        rw [giantSignedTiltedPrimeLaw_eq]
        have h := (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp p) hsmall).1
        nlinarith [markedHarmonicAtom_nonneg P hV (p := p)]
  · calc
      _ ≤ ∑ p : P, markedHarmonicAtom P p * (1 - (n : ℝ) / Pmin)⁻¹ := by
        apply Finset.sum_le_sum
        intro p _
        rw [giantSignedTiltedPrimeLaw_eq]
        exact mul_le_mul_of_nonneg_left
          (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp p) hsmall).2
          (markedHarmonicAtom_nonneg P hV)
      _ = _ := by rw [← Finset.sum_mul, markedHarmonicAtom_sum P hV, one_mul]

theorem giantSignedTiltedPrimeLaw_sum_le_two (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ)
    (hV : 0 < bandReciprocalMass P) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ p : P, Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin ≤ 1 / 2) :
    (∑ p : P, giantSignedTiltedPrimeLaw P q p) ≤ 2 := by
  have hlt : (n : ℝ) / Pmin < 1 := by linarith
  apply (giantSignedTiltedPrimeLaw_sum_bounds P q hV hq0 hq1 Pmin hPmin hp hlt).2.trans
  have hb : 0 < 1 - (n : ℝ) / Pmin := by linarith
  rw [← one_div]
  apply (div_le_iff₀ hb).mpr
  linarith

end
end ArtinMatthews
