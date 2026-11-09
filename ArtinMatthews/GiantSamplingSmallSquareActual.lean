module

public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.GiantSamplingSquarePowers


set_option backward.privateInPublic true
@[expose] public section

/-! The actual small-squarepart sum consumes the source shifted bound
with its literal coefficient and obtains the two terms in (6.3). -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

theorem giantCubicSampling_smallSquareRows_le (η : HeckeFamily.Character)
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε : ℝ)
    (R : ℕ) (K : Finset ℕ) (B : ℕ) {x T D C ν Cν : ℝ}
    (hx : 0 < x) (hT : 0 < T) (hD : 0 ≤ D) (hDT : D ^ 2 ≤ T)
    (hC : 0 < C) (hCν : 0 ≤ Cν)
    (hK : ∀ k ∈ K, T ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * T) (hH : ∀ k ∈ K, ‖H k‖ ≤ C)
    (hbilinear : GiantSamplingShiftedBilinearBound η Φ x ν Cν) :
    (∑ r ∈ Finset.Icc 1 R, ‖giantCubicSamplingSquareRows η χ H Φ ε x r K B
      ((Finset.Icc 1 B).filter (fun d : ℕ => (d : ℝ) ≤ D))‖) ≤
        (R : ℝ) ^ 2 * (M : ℝ) ^ 2 * C * (Cν * x ^ ν) *
          (x * T ^ (-(1 / 2) : ℝ) * D ^ 2 +
            x ^ (7 / 8 : ℝ) * (2 * T) ^ (3 / 8 : ℝ) * (4 * D ^ (1 / 4 : ℝ))) := by
  let P := (Finset.Icc 1 B).filter (fun d : ℕ => (d : ℝ) ≤ D)
  let A := x * T ^ (-(1 / 2) : ℝ)
  let Q := x ^ (7 / 8 : ℝ) * (2 * T) ^ (3 / 8 : ℝ)
  let F := (M : ℝ) ^ 2 * C * (Cν * x ^ ν)
  let S := A * D ^ 2 + Q * (4 * D ^ (1 / 4 : ℝ))
  have hA : 0 ≤ A := mul_nonneg hx.le (Real.rpow_nonneg hT.le _)
  have hQ : 0 ≤ Q := mul_nonneg (Real.rpow_nonneg hx.le _)
    (Real.rpow_nonneg (by positivity) _)
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (sq_nonneg _) hC.le)
    (mul_nonneg hCν (Real.rpow_nonneg hx.le _))
  have hS : 0 ≤ S := add_nonneg (mul_nonneg hA (sq_nonneg _))
    (mul_nonneg hQ (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)))
  have hrow (r : ℕ) (hr : r ∈ Finset.Icc 1 R) :
      ‖giantCubicSamplingSquareRows η χ H Φ ε x r K B P‖ ≤ (r : ℝ) * F * S := by
    let : NeZero r := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hr).1⟩
    unfold giantCubicSamplingSquareRows
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ d ∈ P, (r : ℝ) * F * (A * (d : ℝ) + Q * (d : ℝ) ^ (-(3 / 4) : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd₀ : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have hdD : (d : ℝ) ≤ D := (Finset.mem_filter.mp hd).2
        have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd₀
        have hlo : 1 ≤ T / (d : ℝ) ^ 2 := by
          apply (le_div_iff₀ (pow_pos hdpos 2)).mpr
          rw [one_mul]
          exact (pow_le_pow_left₀ hdpos.le hdD 2).trans hDT
        have h := giantCubicSampling_squareRow_norm_le (r := r) η χ H Φ ε K B d hd₀
          hx hT hC hCν hlo hK hH hbilinear
        obtain ⟨hhalf, hthree⟩ := giantSampling_squarepart_rpow_scales hT hdpos
        rw [hhalf, hthree] at h
        apply h.trans_eq
        dsimp only [F, A, Q]
        ring
      _ = (r : ℝ) * F * (A * (∑ d ∈ P, (d : ℝ)) +
          Q * ∑ d ∈ P, (d : ℝ) ^ (-(3 / 4) : ℝ)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      _ ≤ _ := by
        obtain ⟨h₁, h₂⟩ := giantSampling_smallSquare_power_sums B hD
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left h₁ hA) (mul_le_mul_of_nonneg_left h₂ hQ))
          (mul_nonneg (Nat.cast_nonneg _) hF)
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 1 R, (R : ℝ) * F * S := by
      apply Finset.sum_le_sum
      intro r hr
      exact (hrow r hr).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.mem_Icc.mp hr).2) hF) hS)
    _ = _ := by simp [F, S, A, Q]; ring

end ArtinMatthews
