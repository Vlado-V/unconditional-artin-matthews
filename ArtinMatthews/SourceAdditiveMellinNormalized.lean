module

public import ArtinMatthews.SourceMellinEnergyPairing
public import ArtinMatthews.SourceMellinLogPullbackSobolev
public import Mathlib.Analysis.Real.Pi.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! On a fixed positive interval, the weighted logarithmic Fourier energy
controls the local additive energy. This is the normalized dual form of
Poisson–Dirichlet Lemma 6.4. -/

namespace ArtinMatthews
open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff BigOperators
noncomputable section

theorem sourceAdditiveMellinEnergy_normalized
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) (j : ℕ) (hj : 2 ≤ j) :
    ∃ K > 0, ∀ {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
      (_ : ∀ i ∈ S, x i ∈ Icc c C) (T : ℝ) (_ : 1 ≤ T),
      (∫ t in Icc (-T) T, ‖sourceLocalAdditivePolynomial S x a t‖ ^ 2) ≤
        K * ∫ t : ℝ, markedMajorFourierWeight (T / (2 * Real.pi)) j t *
          ‖sourceLocalAdditivePolynomial S (fun i => Real.log (x i)) a t‖ ^ 2 := by
  let A := 1 + max |Real.log c| |Real.log C|
  have hA : 0 < A := add_pos_of_pos_of_nonneg zero_lt_one ((abs_nonneg _).trans (le_max_left _ _))
  let b : ContDiffBump (0 : ℝ) := ⟨A, A + 1, hA, by linarith⟩
  let χ (u : ℝ) := (b u : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχc : HasCompactSupport χ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  obtain ⟨C₀, hC₀, hlog₀⟩ := sourceMellinLogPullback_derivative_energy χ hχ hχc 0
  obtain ⟨Cⱼ, hCⱼ, hlogⱼ⟩ := sourceMellinLogPullback_derivative_energy χ hχ hχc j
  let P := (2 : ℝ) ^ j * (C₀ + Cⱼ * (4 * Real.pi) ^ (2 * j))
  let K := P + 1
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro ι S x a hx T hT
  have hT₀ : 0 < T := zero_lt_one.trans_le hT
  let W := T / (2 * Real.pi)
  have hW : 0 < W := by dsimp only [W]; positivity
  obtain ⟨q, E, hE, hadd, hband, hq, htest⟩ := sourceAdditiveMellin_dual_test S x a hT₀
  let R := 4 * Real.pi * T
  have hR : 1 ≤ R := by
    have hπ : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
    dsimp only [R]
    exact hπ.trans (le_mul_of_one_le_right (by positivity) hT)
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ q
  have hderiv (k : ℕ) : (∫ u, ‖iteratedDeriv k (g : ℝ → ℂ) u‖ ^ 2) ≤ R ^ (2 * k) * E := by
    have hd := sourceMellinSchwartz_band_derivative_energy q (by linarith : 0 ≤ 2 * T) hband k
    have hr : 2 * Real.pi * (2 * T) = R := by dsimp only [R]; ring
    rw [hr] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left hq (by positivity))
  let G := (sourceMellinLogPullback_hasCompactSupport χ g hχc).toSchwartzMap
    (sourceMellinLogPullback_contDiff χ hχ g)
  have hG : (G : ℝ → ℂ) = fun u => χ u * g (Real.exp u) := rfl
  have hG₀ : (∫ u, ‖G u‖ ^ 2) ≤ C₀ * E := by
    simpa only [← hG, iteratedDeriv_zero, Nat.mul_zero, pow_zero, mul_one] using
      hlog₀ g R E hR hE (fun k _ => hderiv k)
  have hGⱼ : (∫ u, ‖iteratedDeriv j (G : ℝ → ℂ) u‖ ^ 2) ≤ Cⱼ * R ^ (2 * j) * E := by
    simpa only [← hG] using hlogⱼ g R E hR hE (fun k _ => hderiv k)
  let d := ((2 * Real.pi * W)⁻¹) ^ (2 * j)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hscale : d * R ^ (2 * j) = (4 * Real.pi) ^ (2 * j) := by
    dsimp only [d]
    rw [← mul_pow]
    congr 1
    dsimp only [W, R]
    field_simp [Real.pi_ne_zero, hT₀.ne']
  have hfourier : (∫ t : ℝ, (1 + |t| / W) ^ j * ‖(𝓕 G) t‖ ^ 2) ≤ P * E := by
    calc
      _ ≤ (2 : ℝ) ^ j * ((∫ u, ‖G u‖ ^ 2) +
          d * ∫ u, ‖iteratedDeriv j (G : ℝ → ℂ) u‖ ^ 2) :=
        (sourceMellinSchwartz_weighted_fourier_energy G hW j).2
      _ ≤ (2 : ℝ) ^ j * (C₀ * E + d * (Cⱼ * R ^ (2 * j) * E)) :=
        mul_le_mul_of_nonneg_left (add_le_add hG₀ (mul_le_mul_of_nonneg_left hGⱼ hd)) (by positivity)
      _ = (2 : ℝ) ^ j * (C₀ * E + Cⱼ * (d * R ^ (2 * j)) * E) := by ring
      _ = P * E := by rw [hscale]; dsimp only [P]; ring
  have hEval (i : ι) (hi : i ∈ S) : G (Real.log (x i)) = g (x i) := by
    have hxi := hx i hi
    have hpos : 0 < x i := hc.trans_le hxi.1
    have hlo := Real.log_le_log hc hxi.1
    have hhi := Real.log_le_log hpos hxi.2
    have hlog : |Real.log (x i)| ≤ A := by
      rw [abs_le]
      constructor
      · have h₀ := le_max_left |Real.log c| |Real.log C|
        have h₁ := neg_abs_le (Real.log c)
        dsimp only [A]
        linarith
      · have h₀ := le_max_right |Real.log c| |Real.log C|
        have h₁ := le_abs_self (Real.log C)
        dsimp only [A]
        linarith
    have hbone : b (Real.log (x i)) = 1 := b.one_of_mem_closedBall (by
      change Real.log (x i) ∈ Metric.closedBall 0 A
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hlog)
    change (b (Real.log (x i)) : ℂ) * g (Real.exp (Real.log (x i))) = g (x i)
    rw [hbone, Complex.ofReal_one, Real.exp_log hpos, one_mul]
  let F := sourceLocalAdditivePolynomial S (fun i => Real.log (x i)) a
  have hmatch : (E : ℂ) = ∫ t : ℝ, F t * (𝓕 G) t := by
    calc
      _ = ∑ i ∈ S, a i * g (x i) := htest.symm
      _ = ∑ i ∈ S, a i * (𝓕⁻ (𝓕 G)) (Real.log (x i)) := by
        rw [FourierTransform.fourierInv_fourier_eq]
        exact Finset.sum_congr rfl (fun i hi => congrArg (a i * ·) (hEval i hi).symm)
      _ = _ := sourceMellin_inverse_fourier_sum S (fun i => Real.log (x i)) a (𝓕 G)
  have hp := sourceMellin_weighted_pairing_le S (fun i => Real.log (x i)) a G hW hK hj
  change ‖∫ t : ℝ, F t * (𝓕 G) t‖ ≤ _ at hp
  rw [← hmatch, Complex.norm_real, Real.norm_of_nonneg hE] at hp
  have hhalf : (∫ t : ℝ, (1 + |t| / W) ^ j * ‖(𝓕 G) t‖ ^ 2) / (2 * K) ≤ E / 2 := by
    calc
      _ ≤ (P * E) / (2 * K) := div_le_div_of_nonneg_right hfourier (by positivity)
      _ ≤ (K * E) / (2 * K) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hE) (by positivity)
      _ = _ := by field_simp [hK.ne']
  refine hadd.trans ?_
  change E ≤ K * ∫ t : ℝ, markedMajorFourierWeight W j t * ‖F t‖ ^ 2
  nlinarith [hp, hhalf]

end
end ArtinMatthews
