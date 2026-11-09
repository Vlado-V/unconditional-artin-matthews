module

public import ArtinMatthews.GiantSignedBannedIdealBound
public import ArtinMatthews.GiantSignedBanBandBound
public import ArtinMatthews.GiantSignedTiltBandBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The original auxiliary collision probabilities and actual visit-law
densities give an explicit clean ideal bound on the prime bands. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedBannedIdeal_band_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell n : ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (v Pmin : ℝ) (hv : 0 < v) (hPmin : 0 < Pmin)
    (hV : ∀ j, v ≤ bandReciprocalMass (P j)) (hp : ∀ j (p : P j), Pmin ≤ p.val)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : (n : ℝ) / Pmin < 1)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (cost : I → ℝ) (hcost : ∀ i ∈ patterns, 0 ≤ cost i)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ cost i)
    (freshCount comparisonCount : ℕ)
    (hFreshCount : ∀ i ∈ patterns, (∑ j, ((C i j).card + ell)) ≤ freshCount)
    (hComparisonCount : ∀ i ∈ patterns, (∑ j, (C i j).card) * (2 * (k+ell)) ≤ comparisonCount)
    (hDensitySmall : (freshCount : ℝ) * ((n : ℝ) / Pmin) ≤ 1 / 2)
    (U : ℝ) (hU : 0 ≤ U)
    (hOriginal : ∀ f : MarkedPhysicalMarking P (k+ell) → ℂ, IdealSymmetric f →
      idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
        U ^ 2 * idealLabelEnergy P (k+ell) f)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) :
    (∑ a, giantSignedActiveMass (fun j => giantSignedTiltedPrimeLaw (P j) q) a *
      ‖idealOperatorWithLaws (fun j => giantSignedTiltedPrimeLaw (P j) q)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ
        (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0) f a‖ ^ 2) ≤
      ((1 - (n : ℝ) / Pmin)⁻¹) ^ (Fintype.card J * (k+ell)) *
        (U + (∑ i ∈ patterns, cost i) * ((comparisonCount : ℝ) / (v * Pmin)) +
          (2 * (freshCount : ℝ) * ((n : ℝ) / Pmin)) * ∑ i ∈ patterns, cost i) ^ 2 *
        ∑ a, giantSignedActiveMass (fun j => giantSignedTiltedPrimeLaw (P j) q) a * ‖f a‖ ^ 2 := by
  classical
  let r : ∀ j, P j → ℝ := fun _ p => giantSignedPrimeDensity q p.val
  have hδ : 0 ≤ (n : ℝ) / Pmin := div_nonneg (Nat.cast_nonneg _) hPmin.le
  have hr (j : J) (p : P j) : 1 ≤ r j p :=
    (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp j p) hsmall).1
  have hrR (j : J) (p : P j) : r j p ≤ (1 - (n : ℝ) / Pmin)⁻¹ :=
    (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp j p) hsmall).2
  have hBan (i : I) (hi : i ∈ patterns) (a b : MarkedPhysicalMarking P (k+ell)) :
      (∑ aux : GiantTwoSidedPatternAuxiliary P (C i),
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (if GiantSignedAuxiliaryBan (C i) a b aux then 0 else 1 : ℝ)) ≤
        (comparisonCount : ℝ) / (v * Pmin) := by
    refine (giantSignedAuxiliaryBan_band_probability hdis v Pmin hv hPmin hV hp (C i) a b).trans ?_
    apply div_le_div_of_nonneg_right _ (mul_pos hv hPmin).le
    exact_mod_cast hComparisonCount i hi
  have hFresh (i : I) (hi : i ∈ patterns) (b : MarkedPhysicalMarking P (k+ell)) :
      idealFreshTargetMass r (C i) b ≤ 1 + 2 * (freshCount : ℝ) * ((n : ℝ) / Pmin) := by
    have hcount : ((∑ j, ((C i j).card + ell) : ℕ) : ℝ) ≤ freshCount := by
      exact_mod_cast hFreshCount i hi
    have hslots : ((∑ j, ((C i j).card + ell) : ℕ) : ℝ) * ((n : ℝ) / Pmin) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_right hcount hδ).trans hDensitySmall
    have he := giantSignedFreshTilt_band_error q hq0 hq1 Pmin hPmin hp hsmall (C i) hslots b
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 2)) hδ
    change idealFreshTargetMass r (C i) b - 1 ≤ _ at he
    linarith
  have he := giantSignedTiltedBannedIdeal_energy (fun j => hv.trans_le (hV j)) hP
    r hr ((1 - (n : ℝ) / Pmin)⁻¹) (inv_nonneg.mpr (sub_pos.mpr hsmall).le) hrR
    patterns C Θ ζ K cost (fun _ => (comparisonCount : ℝ) / (v * Pmin)) hcost
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (mul_pos hv hPmin).le) hK hBan
    (2 * (freshCount : ℝ) * ((n : ℝ) / Pmin)) U
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hU hFresh hOriginal f hf
  have hlaw : (fun j => giantSignedTiltedPrimeLaw (P j) q) =
      (fun j p => markedHarmonicAtom (P j) p * r j p) := by
    funext j p
    exact giantSignedTiltedPrimeLaw_eq (P j) q p
  rw [hlaw]
  simpa only [Finset.sum_mul] using he

end
end ArtinMatthews
