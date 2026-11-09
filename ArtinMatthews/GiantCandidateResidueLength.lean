module

public import ArtinMatthews.MarkedRoughCharacterRange


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed number of candidate primes costs a subpower modulus.
The positive-power interval retains an exponential length after
division by that modulus. -/

namespace ArtinMatthews
open Filter
open scoped Topology

theorem giant_candidate_residue_double_modulus_le_eventually (C τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, 2*Real.exp (C*L^(9/20:ℝ)) ≤ Real.exp ((τ/2)*L) := by
  have hdecay := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 11/20)).const_mul C
  simp only [mul_zero] at hdecay
  filter_upwards [hdecay.eventually (Iio_mem_nhds (by linarith : 0<τ/4)),
    eventually_ge_atTop (Real.log 2/(τ/4)),eventually_gt_atTop (0:ℝ)] with L hpow hlog hL
  have hs : C*L^(9/20:ℝ) ≤ (τ/4)*L := by
    have h := mul_le_mul_of_nonneg_right hpow.le hL.le
    change (C*L^(-(11/20:ℝ)))*L ≤ (τ/4)*L at h
    have hmul : L^(-(11/20:ℝ))*L = L^(9/20:ℝ) := by
      calc
        _ = L^(-(11/20:ℝ))*L^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hL]; norm_num
    simpa only [mul_assoc,hmul] using h
  have hlog' : Real.log 2 ≤ (τ/4)*L := by
    exact ((div_le_iff₀ (by linarith : 0<τ/4)).mp hlog).trans_eq (mul_comm _ _)
  have htwo : (2:ℝ) ≤ Real.exp ((τ/4)*L) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
    exact Real.exp_le_exp.mpr hlog'
  calc
    _ ≤ Real.exp ((τ/4)*L)*Real.exp ((τ/4)*L) :=
      mul_le_mul htwo (Real.exp_le_exp.mpr hs) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem giantCandidateResidueLength_le {Q H L τ : ℝ} (hQ : 0 < Q)
    (hmod : 2*Q ≤ Real.exp ((τ/2)*L)) (hH : Real.exp (τ*L) ≤ H) :
    Real.exp ((τ/2)*L) ≤ H/(2*Q) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*Q)).mpr
  calc
    _ ≤ Real.exp ((τ/2)*L)*Real.exp ((τ/2)*L) :=
      mul_le_mul_of_nonneg_left hmod (Real.exp_nonneg _)
    _ = Real.exp (τ*L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := hH

end ArtinMatthews
