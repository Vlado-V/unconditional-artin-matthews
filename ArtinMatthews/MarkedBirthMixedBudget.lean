module

public import ArtinMatthews.MarkedMemoryBirthPhaseBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Numerical comparison of the exact mixed edge budget with a rank
budget, and the actual polynomial crude edge envelope at B=ceil(L^2). -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem markedMixedEdgeBudget_mono_count {ε R : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hR : 0 ≤ R) {N m k : ℕ} (hm : m ≤ k) (hk : k ≤ N) :
    ε^(N-m)*R^m ≤ ε^(N-k)*(max 1 R)^k := by
  have hR₁ : 1 ≤ max 1 R := le_max_left _ _
  have hR₀ : 0 ≤ max 1 R := zero_le_one.trans hR₁
  have hexp : N-m=(N-k)+(k-m) := by omega
  have hcount : k=m+(k-m) := by omega
  calc
    _ ≤ ε^(N-m)*(max 1 R)^m := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hR (le_max_right _ _) m) (pow_nonneg hε₀ _)
    _ = ε^(N-k)*ε^(k-m)*(max 1 R)^m := by rw [hexp,pow_add]
    _ ≤ ε^(N-k)*(max 1 R)^(k-m)*(max 1 R)^m := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε₀ (hε₁.trans hR₁) (k-m))
          (pow_nonneg hε₀ _)) (pow_nonneg hR₀ _)
    _ = _ := by
      have hp : (max 1 R)^(k-m)*(max 1 R)^m = (max 1 R)^k := by
        rw [← pow_add]
        congr 1
        omega
      rw [mul_assoc,hp]

theorem markedBirthCrudeEdgeBudget_polynomial (K : ℕ) (v₀ W A G : ℝ)
    (hv₀ : 1 ≤ v₀) (hW : 0 ≤ W) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      markedRawEdgeCrudeActualConstant K v₀ 1 W A 1 *
        (markedDirtyMemoryCutoff x+1:ℝ)^K*((Real.log x)^(G+7))^3 ≤
          (Real.log x)^(2*(K:ℝ)+3*(G+7)+1) := by
  let C := markedRawEdgeCrudeActualConstant K v₀ 1 W A 1 * (3:ℝ)^K
  have hC : 0 ≤ C := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv₀₀ := zero_le_one.trans hv₀
    dsimp [C,markedRawEdgeCrudeActualConstant]
    positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 C))] with x hx
  have hL₁ : 1 ≤ Real.log x := (le_max_left _ _).trans hx
  have hL : 0 < Real.log x := zero_lt_one.trans_le hL₁
  have hCL : C ≤ Real.log x := (le_max_right _ _).trans hx
  have hB : (markedDirtyMemoryCutoff x+1:ℝ) ≤ 3*(Real.log x)^(2:ℝ) := by
    have hh := markedDirtyMemoryCutoff_le hL₁
    have hp : 1 ≤ (Real.log x)^(2:ℝ) := Real.one_le_rpow hL₁ (by norm_num)
    linarith
  have hK₀ : 0 ≤ markedRawEdgeCrudeActualConstant K v₀ 1 W A 1 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv₀₀ := zero_le_one.trans hv₀
    unfold markedRawEdgeCrudeActualConstant
    positivity
  calc
    _ ≤ markedRawEdgeCrudeActualConstant K v₀ 1 W A 1 *
        (3*(Real.log x)^(2:ℝ))^K*((Real.log x)^(G+7))^3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hB K) hK₀) (by positivity)
    _ = C*(Real.log x)^(2*(K:ℝ)+3*(G+7)) := by
      have hp₁ : ((Real.log x)^(2:ℝ))^K = (Real.log x)^(2*(K:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
      have hp₂ : ((Real.log x)^(G+7))^3 = (Real.log x)^(3*(G+7)) := by
        rw [← Real.rpow_mul_natCast hL.le]
        congr 1
        ring
      rw [mul_pow,hp₁,hp₂,Real.rpow_add hL]
      dsimp [C]
      ring
    _ ≤ (Real.log x)*(Real.log x)^(2*(K:ℝ)+3*(G+7)) :=
      mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL.le _)
    _ = _ := by
      conv_lhs => lhs; rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add hL]
      congr 1
      ring

end ArtinMatthews
