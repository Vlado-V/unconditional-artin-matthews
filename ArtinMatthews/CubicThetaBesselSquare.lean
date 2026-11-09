module

public import ArtinMatthews.CubicThetaMeanSquare
public import ArtinMatthews.ShiftedWeightedSquare
public import ArtinMatthews.ShiftedBesselScale


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ideal-theta coefficients satisfy a square-sum bound at the true
Bessel scale, uniformly in the character and source dilation. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

theorem idealTheta_weighted_square (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : SevenEighths.HeckeFamily.Character)
      (S B : ℝ), 0 < S → 0 ≤ B → ∀ b : ℕ → ℂ,
      (∀ n : ℕ, (1 + ((n + 1 : ℕ) : ℝ) / S)^2 * ‖b (n + 1)‖ ≤ B) →
      Summable (fun n : ℕ => ‖idealThetaCoeff χ (n + 1) * b (n + 1)‖^2) ∧
      (∑' n : ℕ, ‖idealThetaCoeff χ (n + 1) * b (n + 1)‖^2) ≤ C * B^2 * S^(1 + ε) := by
  obtain ⟨C, hC, hcoeff⟩ := idealThetaCoeff_square_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro χ S B hS hB b hb
  exact shifted_weighted_square_sum ε S C B hε hεtwo hS hC.le hB
    (idealThetaCoeff χ) b (fun n => hcoeff χ (n + 1)) hb

theorem idealTheta_bessel_square_uniform (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W : SchwartzMap ℝ ℂ)
        (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
      ∀ (K Q : ℝ), 0 < K → 0 < Q →
      Summable (fun n : ℕ => ‖idealThetaCoeff χ (n + 1) *
        weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖^2) ∧
      (∑' n : ℕ, ‖idealThetaCoeff χ (n + 1) *
        weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖^2) ≤
        C * K^2 * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)^2 * (Q / K)^(1 + ε) := by
  obtain ⟨s, Cb, hCb, hweight⟩ := weightOneBesselTransform_dilate_euler_source_bound 2 0
  obtain ⟨Ca, hCa, hsum⟩ := idealTheta_weighted_square ε hε hεtwo
  refine ⟨s, Ca * Cb^2, by positivity, ?_⟩
  intro χ W B hB hWs K Q hK hQ
  let E : ℝ := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hE : 0 ≤ E := apply_nonneg (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)) W
  have hb (n : ℕ) :
      (1 + ((n + 1 : ℕ) : ℝ) / (Q / K))^2 *
        ‖weightOneBesselTransform (fun x => W (x / K)) (((n + 1 : ℕ) : ℝ) / Q)‖ ≤
          Cb * K * E := by
    have h := hweight W B hB hWs K (((n + 1 : ℕ) : ℝ) / Q) hK (by positivity) 0 le_rfl
    have heq : K * (((n + 1 : ℕ) : ℝ) / Q) = ((n + 1 : ℕ) : ℝ) / (Q / K) := by
      field_simp
    simpa only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero,
      mul_one, heq] using h
  obtain ⟨hs, hh⟩ := hsum χ (Q / K) (Cb * K * E) (div_pos hQ hK) (by positivity)
    (fun n => weightOneBesselTransform (fun x => W (x / K)) ((n : ℝ) / Q)) hb
  refine ⟨hs, ?_⟩
  convert hh using 1
  ring

end ArtinMatthews
