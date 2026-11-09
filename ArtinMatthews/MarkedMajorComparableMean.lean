module

public import ArtinMatthews.MarkedMajorMellinLabelEnergy


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Filter MeasureTheory Set
noncomputable section

theorem markedMajorFourierWeight_mono_scale {V W : ℝ} (hV : 0 < V) (hVW : V ≤ W)
    (n : ℕ) (t : ℝ) : markedMajorFourierWeight V n t ≤ markedMajorFourierWeight W n t := by
  have hW : 0 < W := hV.trans_le hVW
  unfold markedMajorFourierWeight
  apply inv_anti₀
  · positivity
  · exact pow_le_pow_left₀ (by positivity)
      (add_le_add_right (div_le_div_of_nonneg_left (abs_nonneg t) hV hVW) 1) n

theorem markedMajorLocalMean_mono_scale (Q : ℝ → ℂ) (hQ : Continuous Q)
    (hB : ∃ B, ∀ t, ‖Q t‖ ≤ B) {V W : ℝ} (hV : 0 < V) (hVW : V ≤ W) (c : ℝ) :
    (∫ t, markedMajorFourierWeight V 2 (t-c)*‖Q t‖^2) ≤
      ∫ t, markedMajorFourierWeight W 2 (t-c)*‖Q t‖^2 := by
  obtain ⟨B,hB⟩ := hB
  exact integral_mono (markedMajorLocalMean_integrable Q hQ B hB hV c)
    (markedMajorLocalMean_integrable Q hQ B hB (hV.trans_le hVW) c)
    (fun t => mul_le_mul_of_nonneg_right (markedMajorFourierWeight_mono_scale hV hVW 2 (t-c)) (sq_nonneg _))

theorem markedMajorLocalMean_mono_radius (Q : ℝ → ℂ) (hQ : Continuous Q)
    {S T : ℝ} (hST : S ≤ T) :
    (∫ t in Icc (-S) S, ‖Q t‖^2) ≤ ∫ t in Icc (-T) T, ‖Q t‖^2 := by
  exact setIntegral_mono_set ((hQ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ h => ⟨(neg_le_neg hST).trans h.1,h.2.trans hST⟩))

theorem markedMajorComparable_central_radius {L X X' B : ℝ}
    (hL : 2 ≤ L) (hX' : 0 ≤ X') (hXX' : X ≤ 2*X') :
    2*X*L^B ≤ 2*X'*L^(B+1) := by
  have hLp : 0 < L := by linarith
  rw [Real.rpow_add hLp,Real.rpow_one]
  have hpow : 0 ≤ L^B := Real.rpow_nonneg hLp.le B
  nlinarith [mul_le_mul_of_nonneg_right hXX' hpow,
    mul_nonneg hX' hpow, mul_nonneg (mul_nonneg hX' hpow) (sub_nonneg.mpr hL)]

end
end ArtinMatthews
