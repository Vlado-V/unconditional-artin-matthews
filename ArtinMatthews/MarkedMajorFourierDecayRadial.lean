module

public import ArtinMatthews.MarkedMajorFourierDecayLift
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual radial Fourier decay from full derivative L1 norms, retaining
the derivative scale W instead of paying a prefactor W to a high power. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

def markedMajorDerivativeL1Sum (g : SchwartzMap (ℝ × ℝ) ℂ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m+1), ∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k g p‖

theorem markedMajorPlaneLift_fourier_power_le (g : SchwartzMap (ℝ × ℝ) ℂ)
    (n : ℕ) (w : MarkedMajorFourierPlane) :
    ‖w‖^n*‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖ ≤
      2^n*markedMajorDerivativeL1Sum g n := by
  let G := markedMajorPlaneLift g
  have H := Real.pow_mul_norm_iteratedFDeriv_fourier_le (G.smooth ⊤)
    (fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume G k n)
    (k := 0) (n := n) le_top le_top w
  have h : ‖w‖^n*‖(𝓕 G : SchwartzMap MarkedMajorFourierPlane ℂ) w‖ ≤
      2^n*(∑ k ∈ Finset.range (n+1), ∫ x : MarkedMajorFourierPlane, ‖iteratedFDeriv ℝ k G x‖) := by
    have hf (k : ℕ) : ((Function.Embedding.sectR (0 : ℕ) ℕ) k).1 = 0 := rfl
    have hnorm (k : ℕ) (x : MarkedMajorFourierPlane) :
        ‖iteratedFDeriv ℝ ((Function.Embedding.sectR (0 : ℕ) ℕ) k).2 G x‖ =
          ‖iteratedFDeriv ℝ k G x‖ := rfl
    simpa [Finset.sum_product, norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe,
      hf,hnorm] using H
  exact h.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k _ => markedMajorPlaneLift_derivative_L1_le g k)) (by positivity))

theorem markedMajorDerivativeL1Sum_le (g : SchwartzMap (ℝ × ℝ) ℂ) (m : ℕ)
    {C W : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ W)
    (hD : ∀ k ≤ m, (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k g p‖) ≤ C*W^k) :
    markedMajorDerivativeL1Sum g m ≤ ((m+1 : ℕ) : ℝ)*C*W^m := by
  unfold markedMajorDerivativeL1Sum
  calc
    _ ≤ ∑ _k ∈ Finset.range (m+1), C*W^m := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      exact (hD k hkm).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW hkm) hC)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

lemma markedMajor_one_add_pow_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    (1+r)^m ≤ 2^m*(1+r^m) := by
  by_cases h : r ≤ 1
  · calc
      _ ≤ (2 : ℝ)^m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2^m*1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by have := pow_nonneg hr m; linarith) (by positivity)
  · calc
      _ ≤ (2*r)^m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2^m*r^m := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem markedMajorPlaneLift_fourier_scaled_radial (g : SchwartzMap (ℝ × ℝ) ℂ)
    (m : ℕ) {C W : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ W)
    (hD : ∀ k ≤ m, (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k g p‖) ≤ C*W^k)
    (w : MarkedMajorFourierPlane) :
    (1+‖w‖/W)^m*‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖ ≤
      (2^m*(1+2^m*((m+1 : ℕ) : ℝ)))*C := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hbase : ‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖ ≤ C := by
    have hh := markedMajorPlaneLift_fourier_power_le g 0 w
    simp only [pow_zero, one_mul, markedMajorDerivativeL1Sum, Nat.zero_add,
      Finset.sum_range_one] at hh
    exact hh.trans (by simpa only [pow_zero, mul_one] using hD 0 (Nat.zero_le m))
  have hhigh : (‖w‖/W)^m*‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖ ≤
      2^m*((m+1 : ℕ) : ℝ)*C := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hWp m)).mpr
    calc
      _ ≤ 2^m*markedMajorDerivativeL1Sum g m := markedMajorPlaneLift_fourier_power_le g m w
      _ ≤ 2^m*(((m+1 : ℕ) : ℝ)*C*W^m) :=
        mul_le_mul_of_nonneg_left (markedMajorDerivativeL1Sum_le g m hC hW hD) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (2^m*(1+(‖w‖/W)^m))*‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖ :=
      mul_le_mul_of_nonneg_right (markedMajor_one_add_pow_le (by positivity) m) (norm_nonneg _)
    _ = 2^m*(‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖+
        (‖w‖/W)^m*‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ) w‖) := by ring
    _ ≤ 2^m*(C+2^m*((m+1 : ℕ) : ℝ)*C) :=
      mul_le_mul_of_nonneg_left (add_le_add hbase hhigh) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews
