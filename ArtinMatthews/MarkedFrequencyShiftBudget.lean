module

public import ArtinMatthews.MarkedRoughCharacterBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform frequency shifts retain the proved high-frequency window.
The lower cutoff depends only on the two polynomial exponents. -/
namespace ArtinMatthews
open Filter
open scoped Topology

lemma marked_frequency_shift_lower {T0 C L t v : ℝ} (hL : 2 ≤ L)
    (ht : L^(max T0 C+2) ≤ |t|) (hv : |v| ≤ L^C) : L^T0 ≤ |t+v| := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h₁ := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left T0 C)
  have h₂ := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right T0 C)
  have hsum : L^T0+L^C ≤ 2*L^(max T0 C) := by linarith
  have hscale : 2*L^(max T0 C) ≤ L^(max T0 C+2) := by
    calc
      _ = L^(max T0 C)*2 := by ring
      _ ≤ L^(max T0 C)*L^2 := mul_le_mul_of_nonneg_left (by nlinarith)
        (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [Real.rpow_add hL0]; norm_num
  have htri := abs_add_le (t+v) (-v)
  simp only [add_neg_cancel_right,abs_neg] at htri
  linarith

lemma marked_frequency_shift_upper_budget (K b C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      K*Real.exp L*L^b+L^C ≤ Real.exp (2*L) := by
  have h₁ := (rpow_mul_exp_neg_rpow_tendsto b
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)).const_mul K
  have h₂ := rpow_mul_exp_neg_rpow_tendsto C
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
  simp only [Real.rpow_one,mul_zero] at h₁ h₂
  have hh := h₁.add h₂
  simp only [zero_add] at hh
  filter_upwards [hh.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with L hL
  have hE₁ : Real.exp (-L)*Real.exp (2*L) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE₂ : Real.exp (-(2*L))*Real.exp (2*L) = 1 := by
    rw [← Real.exp_add]
    simp
  have he : K*Real.exp L*L^b+L^C =
      (K*(L^b*Real.exp (-L))+L^C*Real.exp (-(2*L)))*Real.exp (2*L) := by
    rw [add_mul]
    calc
      _ = K*L^b*(Real.exp (-L)*Real.exp (2*L)) +
          L^C*(Real.exp (-(2*L))*Real.exp (2*L)) := by rw [hE₁,hE₂]; ring
      _ = _ := by ring
  rw [he]
  simpa only [neg_mul,one_mul] using mul_le_mul_of_nonneg_right hL.le (Real.exp_nonneg (2*L))

theorem marked_frequency_shift_window (T0 C b K : ℝ) (hT0 : 0 < T0) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ L : ℝ in atTop, ∀ t v : ℝ,
      L^T ≤ |t| → |t| ≤ K*Real.exp L*L^b → |v| ≤ L^C →
        L^T0 ≤ |t+v| ∧ |t+v| ≤ Real.exp (2*L) := by
  refine ⟨max T0 C+2,by have h := le_max_left T0 C; linarith,?_⟩
  filter_upwards [marked_frequency_shift_upper_budget K b C,
    eventually_ge_atTop (2 : ℝ)] with L hbudget hL t v ht hthi hv
  refine ⟨marked_frequency_shift_lower hL ht hv,?_⟩
  exact (abs_add_le t v).trans ((add_le_add hthi hv).trans hbudget)

end ArtinMatthews
