module

public import ArtinMatthews.CubicSieveModelDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Every fixed logarithmic cost is absorbed by the actual retained
cutoff and the lower endpoint of a fixed marking band. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped Topology

def cubicSieveSourceModelEnvelope (α x : ℝ) : ℝ :=
  (1 / 4 : ℝ) ^ ⌊(Real.log x) ^ (1 / 100 : ℝ)⌋₊ +
    (1 + Real.log x) / Real.exp ((Real.log x) ^ α)

theorem cubicSieve_sourceModelEnvelope_log_tendsto {α : ℝ} (hα : 0 < α) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * cubicSieveSourceModelEnvelope α x)
      atTop (𝓝 0) := by
  have hq := cubicSieve_quarter_floor_log_tendsto (by norm_num : (0 : ℝ) < 1 / 100) A
  have h₀ := cubicSieve_marking_lower_log_tendsto hα A
  have h₁ := cubicSieve_marking_lower_log_tendsto hα (A + 1)
  have h := (hq.add h₀).add h₁
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hL := Real.log_pos hx
  unfold cubicSieveSourceModelEnvelope
  rw [Real.rpow_add hL, Real.rpow_one]
  ring

theorem cubicSieve_sourceModelEnvelope_log_saving {α : ℝ} (hα : 0 < α)
    (C A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      C * (Real.log x) ^ B * cubicSieveSourceModelEnvelope α x ≤ δ * (Real.log x) ^ (-A) := by
  have ht := (cubicSieve_sourceModelEnvelope_log_tendsto hα (A + B)).const_mul C
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hδ), eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hL := Real.log_pos hx₁
  have hpow := Real.rpow_pos_of_pos hL A
  calc
    _ = (C * (Real.log x) ^ (A + B) * cubicSieveSourceModelEnvelope α x) *
        (Real.log x) ^ (-A) := by
      rw [Real.rpow_add hL, Real.rpow_neg hL.le]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [mul_assoc] using hx.le) (Real.rpow_nonneg hL.le _)

end ArtinMatthews
