module

public import ArtinMatthews.GiantBoundedProgression
public import ArtinMatthews.MarkedCorrelationNormalization
public import ArtinMatthews.FixedFinitePrimeExceptions
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Support


set_option backward.privateInPublic true
@[expose] public section

/-! The literal p-1 shift costs only a bounded finite-sum error for a fixed
smooth compact test, hence is negligible at x/log(x). No prime theorem is
needed for this shift: the elementary cardinal bound suffices. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology Asymptotics

def giantPrimeMeanRange (T x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 (⌊T*x⌋₊+1)).filter Nat.Prime

def giantShiftedPrimeTest {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x, (Φ (((p : ℝ)-1)/x) : ℂ) * giantUnitResidueIndicator U p

def giantUnshiftedPrimeTest {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x, (Φ ((p : ℝ)/x) : ℂ) * giantUnitResidueIndicator U p

theorem giantPrimeMeanRange_card_bound {T x : ℝ} (hT : 0≤T) (hx : 0≤x) :
    ((giantPrimeMeanRange T x).card : ℝ) ≤ T*x+2 := by
  have hcard : (giantPrimeMeanRange T x).card ≤ ⌊T*x⌋₊+2 := by
    simpa [giantPrimeMeanRange, Nat.card_Icc, Nat.add_assoc] using
      Finset.card_filter_le (Finset.Icc 0 (⌊T*x⌋₊+1)) Nat.Prime
  have hcast := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at hcast
  linarith [Nat.floor_le (mul_nonneg hT hx)]

theorem giant_compact_test_lipschitz (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hc : HasCompactSupport Φ) :
    ∃ K : NNReal, LipschitzWith K Φ := by
  obtain ⟨C,hC⟩ := ((hc.deriv.isCompact_range hderiv).image continuous_norm).bddAbove
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K,lipschitzWith_of_nnnorm_deriv_le hΦ ?_⟩
  intro t
  apply NNReal.coe_le_coe.mp
  exact (hC ⟨deriv Φ t, ⟨t,rfl⟩, rfl⟩).trans (le_max_left _ _)

theorem giant_prime_shift_error_bound {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) {K : NNReal} (hΦ : LipschitzWith K Φ)
    {T x : ℝ} (hT : 0≤T) (hx : 1≤x) :
    ‖giantShiftedPrimeTest U Φ T x - giantUnshiftedPrimeTest U Φ T x‖ ≤ (K : ℝ)*(T+2) := by
  have hx0 : 0<x := zero_lt_one.trans_le hx
  have hterm (p : ℕ) : |Φ (((p : ℝ)-1)/x)-Φ ((p : ℝ)/x)| ≤ (K : ℝ)/x := by
    have h := hΦ.norm_sub_le (((p : ℝ)-1)/x) ((p : ℝ)/x)
    have he : ((p : ℝ)-1)/x-(p : ℝ)/x = -(1/x) := by ring
    have hdist : ‖((p : ℝ)-1)/x-(p : ℝ)/x‖ = 1/x := by
      rw [Real.norm_eq_abs, he, abs_neg, abs_of_pos (one_div_pos.mpr hx0)]
    rw [hdist] at h
    simpa only [Real.norm_eq_abs, mul_one_div] using h
  unfold giantShiftedPrimeTest giantUnshiftedPrimeTest
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ giantPrimeMeanRange T x,
        ‖(Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p -
          (Φ ((p : ℝ)/x) : ℂ)*giantUnitResidueIndicator U p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ giantPrimeMeanRange T x, (K : ℝ)/x := by
      apply Finset.sum_le_sum
      intro p _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hterm p) (giantUnitResidueIndicator_norm_le U p)
        (norm_nonneg _) (div_nonneg K.2 hx0.le)).trans_eq (mul_one _)
    _ = (giantPrimeMeanRange T x).card * ((K : ℝ)/x) := by simp
    _ ≤ (T*x+2)*((K : ℝ)/x) := mul_le_mul_of_nonneg_right
      (giantPrimeMeanRange_card_bound hT hx0.le) (div_nonneg K.2 hx0.le)
    _ ≤ (K : ℝ)*(T+2) := by
      have htwo : (2 : ℝ)≤2*x := by linarith
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hx0).mpr
      nlinarith [mul_nonneg K.2 (sub_nonneg.mpr htwo)]

theorem giant_prime_shift_isLittleO {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) {T : ℝ} (hT : 0≤T) :
    (fun x => giantShiftedPrimeTest U Φ T x - giantUnshiftedPrimeTest U Φ T x)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  obtain ⟨K,hK⟩ := giant_compact_test_lipschitz Φ hΦ hderiv hc
  apply marked_correlation_isLittleO_of_normalized_norm
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.mul_const ((K : ℝ)*(T+2))
  simp only [id_eq, zero_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (by linarith)) (norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left (giant_prime_shift_error_bound U Φ hK hT hx.le)
      (div_nonneg (Real.log_pos hx).le (by linarith))

end
end ArtinMatthews
