module

public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedTiltError


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform bounds for the actual prime law use the true visit count and
the lower edge of the prime bands. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedPrime_deficit_le {n p : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : Pmin ≤ p) :
    giantSignedVisitLoss q / p ≤ (n : ℝ) / Pmin := by
  have hpp : 0 < (p : ℝ) := hPmin.trans_le hp
  calc
    _ ≤ (n : ℝ) / p := div_le_div_of_nonneg_right (giantSignedVisitLoss_le q hq) hpp.le
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hPmin hp

theorem giantSignedPrimeDensity_band_bounds {n p : ℕ} (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : Pmin ≤ p) (hsmall : (n : ℝ) / Pmin < 1) :
    1 ≤ giantSignedPrimeDensity q p ∧
      giantSignedPrimeDensity q p ≤ (1 - (n : ℝ) / Pmin)⁻¹ := by
  have hpp : 0 < p := by exact_mod_cast hPmin.trans_le hp
  exact giantSignedPrimeDensity_bounds q hpp hq1
    (giantSignedPrime_deficit_le q hq0 Pmin hPmin hp) hsmall

theorem giantSignedFreshTilt_band_error
    {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell n : ℕ}
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ j (p : P j), Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin < 1) (C : J → Finset (Fin k))
    (hslots : ((∑ j, ((C j).card + ell) : ℕ) : ℝ) * ((n : ℝ) / Pmin) ≤ 1 / 2)
    (a : MarkedPhysicalMarking P (k+ell)) :
    idealFreshTargetMass (fun _ p => giantSignedPrimeDensity q p.val) C a - 1 ≤
      2 * ((∑ j, ((C j).card + ell) : ℕ) : ℝ) * ((n : ℝ) / Pmin) := by
  apply idealFreshTargetMass_deficit_error _ _ ((n : ℝ) / Pmin)
    (div_nonneg (Nat.cast_nonneg _) hPmin.le) hsmall _ C hslots a
  · intro j p
    exact zero_le_one.trans (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp j p) hsmall).1
  · intro j p
    exact (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp j p) hsmall).2

end
end ArtinMatthews
