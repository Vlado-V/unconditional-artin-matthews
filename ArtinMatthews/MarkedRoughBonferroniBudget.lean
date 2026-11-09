module

public import ArtinMatthews.MarkedRoughCharacterRange


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized finite-sieve remainder at the actual logarithmic depth. -/

namespace ArtinMatthews

open Filter
open scoped Topology

lemma marked_rough_factorial_tail_log_bound {C D L : ℝ} (hC : 0 ≤ C)
    (hL : 0 < L) (hClog : C ≤ Real.log L) :
    markedFactorialTail C (⌊D*Real.log L⌋₊+1) ≤ L^(2-D*Real.log 2) := by
  have hn : D*Real.log L ≤ ((⌊D*Real.log L⌋₊+1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (D*Real.log L)).le
  calc
    _ ≤ Real.exp (2*C)*Real.exp (-Real.log 2*(D*Real.log L)) :=
      markedFactorialTail_le_exp hC _ hn
    _ ≤ Real.exp (2*Real.log L)*Real.exp (-Real.log 2*(D*Real.log L)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, Real.rpow_def_of_pos hL]; congr 1; ring

noncomputable def markedRoughBonferroniEnvelope (K R τ D L : ℝ) : ℝ :=
  2*K*L^(R+2-D*Real.log 2)+K*L^R*Real.exp (-(τ/2)*L)

theorem marked_rough_bonferroni_le_envelope (K R τ D κ : ℝ)
    (hτ : 0 < τ) (hD : 0 ≤ D) (hκ : κ < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ C V H : ℝ,
      0 ≤ C → C ≤ Real.log L → 0 < V → 1/V ≤ K*L^R → Real.exp (τ*L) ≤ H →
      2*markedFactorialTail C (⌊D*Real.log L⌋₊+1)/V +
        (Real.exp (L^κ))^(⌊D*Real.log L⌋₊+1)/(H*V) ≤
        markedRoughBonferroniEnvelope K R τ D L := by
  filter_upwards [marked_rough_log_depth_support D κ (τ/2) hD hκ (half_pos hτ),
    eventually_gt_atTop (0 : ℝ)] with L hdepth hL C V H hC hClog hV hpoly hH
  have hH0 : 0 < H := (Real.exp_pos _).trans_le hH
  have hpoly0 : 0 ≤ K*L^R := (div_nonneg zero_le_one hV.le).trans hpoly
  have htail := marked_rough_factorial_tail_log_bound (D := D) hC hL hClog
  have hlength : (Real.exp (L^κ))^(⌊D*Real.log L⌋₊+1)/H ≤ Real.exp (-(τ/2)*L) := by
    calc
      _ ≤ Real.exp ((τ/2)*L)/Real.exp (τ*L) :=
        div_le_div₀ (by positivity) hdepth (Real.exp_pos _) hH
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  unfold markedRoughBonferroniEnvelope
  calc
    _ ≤ 2*L^(2-D*Real.log 2)*(K*L^R)+Real.exp (-(τ/2)*L)*(K*L^R) := by
      apply add_le_add
      · have hh := mul_le_mul (mul_le_mul_of_nonneg_left htail (by norm_num : (0:ℝ)≤2))
          hpoly (div_nonneg zero_le_one hV.le) (by positivity : 0 ≤ 2*L^(2-D*Real.log 2))
        simpa only [div_eq_mul_inv, one_mul] using hh
      · have hh := mul_le_mul hlength hpoly (div_nonneg zero_le_one hV.le)
          (Real.exp_nonneg (-(τ/2)*L))
        convert hh using 1
        ring
    _ = _ := by
      have hp : L^(2-D*Real.log 2)*L^R = L^(R+2-D*Real.log 2) := by
        rw [← Real.rpow_add hL]
        congr 1
        ring
      calc
        _ = 2*K*(L^(2-D*Real.log 2)*L^R)+K*L^R*Real.exp (-(τ/2)*L) := by ring
        _ = _ := by rw [hp]

theorem marked_rough_bonferroni_envelope_tendsto (K R τ D P : ℝ)
    (hτ : 0 < τ) (hD : R+P+2 < D*Real.log 2) :
    Tendsto (fun L : ℝ => L^P*markedRoughBonferroniEnvelope K R τ D L) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (show 0 < D*Real.log 2-R-P-2 by linarith)).const_mul (2*K)
  have h₂ := (rpow_mul_exp_neg_rpow_tendsto (P+R)
    (by norm_num : (0:ℝ)<1) (half_pos hτ)).const_mul K
  simp only [Real.rpow_one, mul_zero] at h₂
  have hh := h₁.add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hp₁ : L^(-(D*Real.log 2-R-P-2)) = L^P*L^(R+2-D*Real.log 2) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hp₂ : L^(P+R) = L^P*L^R := Real.rpow_add hL _ _
  change 2*K*L^(-(D*Real.log 2-R-P-2)) + K*(L^(P+R)*Real.exp (-(τ/2)*L)) = _
  unfold markedRoughBonferroniEnvelope
  rw [hp₁, hp₂]
  ring

theorem marked_rough_bonferroni_uniform_power_of_depth (K R τ D κ P c : ℝ)
    (hτ : 0 < τ) (hD0 : 0 ≤ D) (hκ : κ < 1)
    (hD : R+P+2 < D*Real.log 2) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ C V H : ℝ,
      0 ≤ C → C ≤ Real.log L → 0 < V → 1/V ≤ K*L^R → Real.exp (τ*L) ≤ H →
      2*markedFactorialTail C (⌊D*Real.log L⌋₊+1)/V +
        (Real.exp (L^κ))^(⌊D*Real.log L⌋₊+1)/(H*V) ≤ c*L^(-P) := by
  have hs := (marked_rough_bonferroni_envelope_tendsto K R τ D P hτ hD).eventually
    (Iio_mem_nhds hc)
  filter_upwards [hs, marked_rough_bonferroni_le_envelope K R τ D κ hτ hD0 hκ,
    eventually_gt_atTop (0 : ℝ)] with L hs henv hL C V H hC hClog hV hpoly hH
  have hpow : 0 < L^P := Real.rpow_pos_of_pos hL P
  have he := henv C V H hC hClog hV hpoly hH
  have hid : L^P*L^(-P) = 1 := by rw [← Real.rpow_add hL]; simp
  apply (mul_le_mul_iff_of_pos_left hpow).mp
  calc
    _ ≤ L^P*markedRoughBonferroniEnvelope K R τ D L := mul_le_mul_of_nonneg_left he hpow.le
    _ ≤ c := hs.le
    _ = _ := by rw [mul_left_comm, hid, mul_one]

theorem marked_rough_bonferroni_uniform_power (K R τ κ P c : ℝ)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hτ : 0 < τ) (hκ : κ < 1) (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ L : ℝ in atTop, ∀ C V H : ℝ,
      0 ≤ C → C ≤ Real.log L → 0 < V → 1/V ≤ K*L^R → Real.exp (τ*L) ≤ H →
      2*markedFactorialTail C (⌊D*Real.log L⌋₊+1)/V +
        (Real.exp (L^κ))^(⌊D*Real.log L⌋₊+1)/(H*V) ≤ c*L^(-P) := by
  let D := (R+P+3)/Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 < D := div_pos (by linarith) hlog
  refine ⟨D, hD0, marked_rough_bonferroni_uniform_power_of_depth K R τ D κ P c
    hτ hD0.le hκ ?_ hc⟩
  dsimp [D]
  rw [div_mul_cancel₀ _ hlog.ne']
  linarith

end ArtinMatthews
