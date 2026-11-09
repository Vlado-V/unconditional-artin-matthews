module

public import ArtinMatthews.CubicThetaBesselSquareAll


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the actual ideal-theta Bessel coefficients.
This uses their proved polynomial bound and the third-order Bessel decay,
independently of the remaining modular transformation law. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

theorem thetaBesselCoeff_summable (χ : SevenEighths.HeckeFamily.Character)
    (W : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hW : Function.support W ⊆ Icc 0 B)
    (K Q : ℝ) (hK : 0 < K) (hQ : 0 < Q) :
    Summable (thetaBesselCoeff χ W K Q) := by
  obtain ⟨s, C, hC, hdecay⟩ := weightOneBesselTransform_dilate_euler_source_bound 3 0
  let S : ℝ := Q / K
  let E : ℝ := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let V : ℝ := C * K * E
  have hS : 0 < S := div_pos hQ hK
  have hE : 0 ≤ E := apply_nonneg (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)) W
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmajor (n : ℕ) : ‖thetaBesselCoeff χ W K Q (n + 1)‖ ≤
      (128 * S * V) * (1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) := by
    let t : ℝ := 1 + ((n + 1 : ℕ) : ℝ) / S
    have ht : 0 < t := by dsimp [t]; positivity
    have hn : ((n + 1 : ℕ) : ℝ) ≤ S * t := by
      dsimp [t]
      field_simp
      nlinarith
    have ha : ‖idealThetaCoeff χ (n + 1)‖ ≤ 128 * ((n + 1 : ℕ) : ℝ) := by
      have ha := idealThetaCoeff_norm_le χ (n + 1)
      push_cast at ha ⊢
      nlinarith
    have hd : t^3 * ‖weightOneBesselTransform (fun x => W (x / K))
        (((n + 1 : ℕ) : ℝ) / Q)‖ ≤ V := by
      have hd := hdecay W B hB hW K (((n + 1 : ℕ) : ℝ) / Q) hK (by positivity) 0 le_rfl
      have heq : K * (((n + 1 : ℕ) : ℝ) / Q) = ((n + 1 : ℕ) : ℝ) / S := by
        dsimp [S]
        field_simp
      simpa only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero,
        Real.exp_zero, mul_one, heq] using hd
    rw [mul_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    rw [thetaBesselCoeff, norm_mul]
    calc
      _ ≤ (128 * (S * t)) *
          ‖weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖ * t^2 := by
        gcongr
        exact ha.trans (by gcongr)
      _ = (128 * S) * (t^3 *
          ‖weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖) := by ring
      _ ≤ 128 * S * V := mul_le_mul_of_nonneg_left hd (by positivity)
  have hs := ((shifted_reciprocal_square_sum S hS).1.mul_left (128 * S * V))
  have hnorm : Summable (fun n : ℕ => ‖thetaBesselCoeff χ W K Q (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor hs
  exact (summable_nat_add_iff 1).mp hnorm.of_norm

end ArtinMatthews
