module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeDeterminant
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Actual delta edge coefficient contraction, retaining the true outgoing
memory damping for subsequent indexed-promotion summation. -/
noncomputable section
namespace ArtinMatthews

theorem markedDirtyRawEdge_delta_detector_norm_le (ψ : ℝ → ℂ) (Y : ℝ) {W : ℝ}
    (hW : 0 ≤ W) (hψ : ∀ t, ‖ψ t‖ ≤ W) (b a t : ℤ) :
    ‖markedRawEdgeDeltaDetector ψ Y b a t‖ ≤ W := by
  classical
  unfold markedRawEdgeDeltaDetector
  split_ifs
  · simpa only [mul_one] using hψ ((t:ℝ)/Y)
  · simpa only [mul_zero,norm_zero] using hW

theorem markedDirtyRawEdge_delta_coefficient_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y : ℝ)
    {ρ H W : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s choice‖ ≤
      H^2*W*ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice)
        choice.target.1 (hZ _ choice.target.2)) := by
  classical
  by_cases hn : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s choice=0
  · rw [hn,norm_zero]
    positivity
  have hs := markedDirtyRawEdge_delta_support hZ ψ η d₀ Y ρ χ s choice hn
  have hD : 0 < (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ) := by
    exact_mod_cast markedRawCopiedProduct_pos ((markedRawActiveSplit pads) s.2.1).1
  have hd₀ : 0 ≤ d₀ := by linarith [hs.1.2]
  have hscale : ‖((d₀/(markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg hd₀ hD.le)]
    exact (div_le_one hD).mpr hs.1.1
  have hsource := markedRawPendingDamping_norm_le s.2.2 s.1.1 (hZ _ s.1.2) hρ₀ hρ₁
  have hsourceEndpoint := markedRawEndpointFactor_norm_le hZ (by norm_num : (0:ℝ)≤1) le_rfl χ hχ s
  have htargetEndpoint := markedRawEndpointFactor_norm_le hZ (by norm_num : (0:ℝ)≤1) le_rfl χ hχ
    (markedRawEdgeTargetState hZ s choice)
  have htarget : ‖((ρ^(markedRawPendingHits (markedRawEdgeTargetState hZ s choice).2.2
      (markedRawEdgeTargetState hZ s choice).1.1 (hZ _ (markedRawEdgeTargetState hZ s choice).1.2)):ℝ):ℂ)‖ =
      ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice) choice.target.1 (hZ _ choice.target.2)) := by
    rw [Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hρ₀ _)]
    rfl
  have hdiv : (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ) ∣
      markedMinorIntegerDet s.1.1 (markedRawEdgeTargetState hZ s choice).1.1 := hs.2.1
  unfold markedRawEdgeChoiceDetectorCoefficient
  dsimp only
  rw [ite_eq_left hs.1,ite_eq_left hdiv,ite_eq_right hs.2.2.1]
  simp only [norm_mul,htarget]
  calc
    _ ≤ 1*1*1*H*H*W*(ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice)
          choice.target.1 (hZ _ choice.target.2)))*1 := by
      gcongr <;> first
        | exact hscale
        | exact hsource
        | exact hsourceEndpoint
        | exact htargetEndpoint
        | apply hη
        | exact markedDirtyRawEdge_delta_detector_norm_le ψ Y hW hψ _ _ _
    _ = _ := by ring

end ArtinMatthews
