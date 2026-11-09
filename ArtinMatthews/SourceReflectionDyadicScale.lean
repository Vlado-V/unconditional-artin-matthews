module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The common dyadic cutoff and its exact Section 04 scale inequalities. -/
namespace ArtinMatthews.SourceEulerAssembly
noncomputable section

def sourceReflectionLength (Z P D : ℝ) : ℝ := 8 * D ^ 2 * P / Z

def sourceReflectionCutoff (Z P D δ : ℝ) : ℝ := Z ^ δ * sourceReflectionLength Z P D

def sourceReflectionTailScale (Z P D δ : ℝ) : ℝ :=
  max (Z ^ δ) (sourceReflectionLength Z P D)⁻¹

theorem sourceReflectionLength_pos {Z P D : ℝ} (hZ : 0 < Z) (hP : 0 < P) (hD : 0 < D) :
    0 < sourceReflectionLength Z P D := by
  unfold sourceReflectionLength
  positivity

theorem sourceReflectionRowScale_le {Z P D d f : ℝ} (hZ : 0 < Z)
    (hd : 0 ≤ d) (hdD : d ≤ 2 * D)
    (hfP : f ^ 2 ≤ 2 * P) :
    d ^ 2 * f ^ 2 / Z ≤ sourceReflectionLength Z P D := by
  have hd₂ : d ^ 2 ≤ (2 * D) ^ 2 := pow_le_pow_left₀ hd hdD 2
  unfold sourceReflectionLength
  apply div_le_div_of_nonneg_right _ hZ.le
  exact (mul_le_mul hd₂ hfP (sq_nonneg f) (by positivity)).trans_eq (by ring)

theorem sourceReflectionCutoff_empty {Z P D δ Q : ℝ} (hQ : 1 ≤ Q)
    (hR : sourceReflectionCutoff Z P D δ < 1) :
    sourceReflectionCutoff Z P D δ < Q := hR.trans_le hQ

theorem sourceReflectionTailScale_le_ratio {Z P D δ Q t : ℝ} (hZ : 0 < Z)
    (ht : 0 < t) (htL : t ≤ sourceReflectionLength Z P D)
    (hQ : 1 ≤ Q) (hQR : sourceReflectionCutoff Z P D δ < Q) :
    sourceReflectionTailScale Z P D δ ≤ Q / t := by
  unfold sourceReflectionTailScale
  apply max_le
  · apply (le_div_iff₀ ht).2
    exact (mul_le_mul_of_nonneg_left htL (Real.rpow_nonneg hZ.le δ)).trans hQR.le
  · have hL : 0 < sourceReflectionLength Z P D := ht.trans_le htL
    exact (inv_le_inv₀ hL ht).2 htL |>.trans (by
      rw [← one_div t]
      exact div_le_div_of_nonneg_right hQ ht.le)

theorem sourceReflectionTailKernel_le {Z P D δ Q t N σ : ℝ} (hZ : 0 < Z)
    (ht : 0 < t) (htL : t ≤ sourceReflectionLength Z P D)
    (hQ : 1 ≤ Q) (hQR : sourceReflectionCutoff Z P D δ < Q) (hN : σ ≤ N) :
    (Q / t) ^ (-N) ≤ sourceReflectionTailScale Z P D δ ^ (-(N - σ)) * (t / Q) ^ σ := by
  have hJ : 0 < sourceReflectionTailScale Z P D δ :=
    (Real.rpow_pos_of_pos hZ δ).trans_le (le_max_left _ _)
  have hQt : 0 < Q / t := div_pos (zero_lt_one.trans_le hQ) ht
  have hle := sourceReflectionTailScale_le_ratio hZ ht htL hQ hQR
  have hs : (Q / t) ^ (-σ) = (t / Q) ^ σ := by
    rw [Real.rpow_neg hQt.le, ← Real.inv_rpow hQt.le, inv_div]
  rw [show -N = -(N - σ) + -σ by ring, Real.rpow_add hQt, hs]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hJ hle (by linarith))
    (Real.rpow_nonneg (div_nonneg ht.le (zero_le_one.trans hQ)) _)

theorem sourceReflectionLength_le {Z P D K M : ℝ} (hZ : 1 ≤ Z)
    (hP : 1 ≤ P) (hD : 1 ≤ D) (hPD : P * D ≤ K * Z ^ M) :
    sourceReflectionLength Z P D ≤ 8 * K ^ 2 * Z ^ (2 * M - 1) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 0 ≤ P := zero_le_one.trans hP
  have hd : 0 ≤ D := zero_le_one.trans hD
  have hk : 0 ≤ K * Z ^ M := (mul_nonneg hp hd).trans hPD
  have hD' : D ≤ K * Z ^ M := (by nlinarith only [hP, hd] : D ≤ P * D).trans hPD
  have hb := mul_le_mul hPD hD' hd hk
  unfold sourceReflectionLength
  calc
    _ = 8 * ((P * D) * D) / Z := by ring
    _ ≤ 8 * ((K * Z ^ M) * (K * Z ^ M)) / Z :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hz.le
    _ = 8 * K ^ 2 * Z ^ (2 * M - 1) := by
      rw [show (2 * M - 1) = (M + M) - 1 by ring, Real.rpow_sub hz, Real.rpow_add hz,
        Real.rpow_one]
      ring

theorem sourceReflectionCutoff_le {Z P D K M δ : ℝ} (hZ : 1 ≤ Z)
    (hP : 1 ≤ P) (hD : 1 ≤ D) (hPD : P * D ≤ K * Z ^ M) :
    sourceReflectionCutoff Z P D δ ≤ 8 * K ^ 2 * Z ^ (2 * M - 1 + δ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  unfold sourceReflectionCutoff
  calc
    _ ≤ Z ^ δ * (8 * K ^ 2 * Z ^ (2 * M - 1)) :=
      mul_le_mul_of_nonneg_left (sourceReflectionLength_le hZ hP hD hPD) (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [Real.rpow_add hz]; ring

theorem sourceReflectionWeightedCutoff_le {Z P D K M δ : ℝ} (hZ : 1 ≤ Z)
    (hP : 1 ≤ P) (hD : 1 ≤ D) (hPD : P * D ≤ K * Z ^ M) :
    D * sourceReflectionCutoff Z P D δ ≤ 8 * K ^ 3 * Z ^ (3 * M - 1 + δ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hd : 0 ≤ D := zero_le_one.trans hD
  have hD' : D ≤ K * Z ^ M := (by nlinarith only [hP, hd] : D ≤ P * D).trans hPD
  have hR : 0 ≤ sourceReflectionCutoff Z P D δ := by
    unfold sourceReflectionCutoff sourceReflectionLength
    positivity
  calc
    _ ≤ (K * Z ^ M) * (8 * K ^ 2 * Z ^ (2 * M - 1 + δ)) :=
      mul_le_mul hD' (sourceReflectionCutoff_le hZ hP hD hPD) hR (hd.trans hD')
    _ = _ := by
      have he : Z ^ (3 * M - 1 + δ) = Z ^ M * Z ^ (2 * M - 1 + δ) := by
        rw [← Real.rpow_add hz]
        congr 1
        ring
      rw [he]
      ring

theorem sourceReflectionSieveLength_le {Z P D δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 ≤ δ)
    (hD : 0 ≤ D) :
    D + sourceReflectionCutoff Z P D δ ≤ 8 * Z ^ δ * (D + D ^ 2 * P / Z) := by
  have he : 1 ≤ Z ^ δ := Real.one_le_rpow hZ hδ
  unfold sourceReflectionCutoff sourceReflectionLength
  have hd : D ≤ (8 * Z ^ δ) * D := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show 1 ≤ 8 * Z ^ δ by linarith) hD
  calc
    D + Z ^ δ * (8 * D ^ 2 * P / Z) ≤
        (8 * Z ^ δ) * D + Z ^ δ * (8 * D ^ 2 * P / Z) := add_le_add hd le_rfl
    _ = _ := by ring

theorem sourceReflectionMainScale_le {Z P D K M : ℝ} (hZ : 1 ≤ Z) (hK : 1 ≤ K)
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hD : 1 ≤ D) (hPD : P * D ≤ K * Z ^ M) :
    Real.sqrt P * (D + D ^ 2 * P / Z) ≤ (K + K ^ 2) * Z ^ (2 * M - 1) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp := zero_le_one.trans hP
  have hd := zero_le_one.trans hD
  have hk := zero_le_one.trans hK
  have hsp : Real.sqrt P ≤ P := Real.sqrt_le_self_iff.mpr (Or.inr hP)
  have hfirst : Real.sqrt P * D ≤ K * Z ^ (2 * M - 1) :=
    ((mul_le_mul_of_nonneg_right hsp hd).trans hPD).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hk)
  have hsquare : (P * D) ^ 2 ≤ (K * Z ^ M) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hp hd) hPD 2
  have hsecond : Real.sqrt P * (D ^ 2 * P / Z) ≤ K ^ 2 * Z ^ (2 * M - 1) := by
    have hds : 0 ≤ D ^ 2 * P := by positivity
    have hb : Real.sqrt P * (D ^ 2 * P) ≤ (P * D) ^ 2 :=
      (mul_le_mul_of_nonneg_right hsp hds).trans_eq (by ring)
    calc
      _ ≤ (K * Z ^ M) ^ 2 / Z := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (hb.trans hsquare) hz.le
      _ = _ := by
        rw [show 2 * M - 1 = (M + M) - 1 by ring, Real.rpow_sub hz, Real.rpow_add hz,
          Real.rpow_one]
        ring
  rw [mul_add, add_mul]
  exact add_le_add hfirst hsecond

end
end ArtinMatthews.SourceEulerAssembly
