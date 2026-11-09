module

public import ArtinMatthews.HeckePrimeLongParameters


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed positive power saving is uniform over every scale above x^δ
and absorbs every prescribed power of log x. -/

namespace ArtinMatthews
open Filter
open scoped Topology

theorem heckePrime_uniform_power_log_saving (K σ δ A : ℝ)
    (hK : 0 ≤ K) (hσ : σ < 1) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ H : ℝ, x^δ ≤ H →
      K*H^σ ≤ H*(Real.log x)^(-A) := by
  let r := δ*(1-σ)
  have hr : 0 < r := mul_pos hδ (sub_pos.mpr hσ)
  have hlim := ((isLittleO_log_rpow_rpow_atTop A hr).tendsto_div_nhds_zero).const_mul K
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro H hH
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hHp : 0 < H := (Real.rpow_pos_of_pos hx0 δ).trans_le hH
  have hsmall : K*x^(-r) ≤ (Real.log x)^(-A) := by
    have hmul : (K*x^(-r))*(Real.log x)^A ≤ 1 := by
      simpa only [Real.rpow_neg hx0.le, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hx.le
    have h := (le_div_iff₀ (Real.rpow_pos_of_pos hlog A)).mpr hmul
    simpa only [one_div, Real.rpow_neg hlog.le] using h
  have hdecay : H^(σ-1) ≤ x^(-r) := by
    calc
      _ ≤ (x^δ)^(σ-1) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hx0 δ) hH (by linarith)
      _ = _ := by rw [← Real.rpow_mul hx0.le]; congr 1; dsimp [r]; ring
  have heq : H*H^(σ-1) = H^σ := by
    calc
      _ = H^(1 : ℝ)*H^(σ-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hHp]; congr 1; ring
  calc
    K*H^σ = H*(K*H^(σ-1)) := by rw [mul_left_comm, heq]
    _ ≤ H*(K*x^(-r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdecay hK) hHp.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hHp.le

end ArtinMatthews
