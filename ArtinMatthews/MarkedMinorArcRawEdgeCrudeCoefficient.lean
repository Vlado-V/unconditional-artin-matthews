module

public import ArtinMatthews.MarkedMinorArcDirtyMajorSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The full literal edge coefficient contracts to its actual scalar
detector. No determinant condition is assigned to a non-delta detector. -/
noncomputable section
namespace ArtinMatthews

theorem markedRawEdgeCrude_detector_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y : ℝ)
    {ρ H : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hη : ∀ t, ‖η t‖ ≤ H)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (detector : ℤ → ℤ → ℤ → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ detector s choice‖ ≤ H^2*
      ‖detector (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2)
        (markedRawLastProduct (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh))
        (markedMinorIntegerDet s.1.1 choice.target.1/
          (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ))‖ := by
  classical
  by_cases hn : markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ detector s choice=0
  · rw [hn,norm_zero]
    positivity
  have hs := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ detector s choice hn
  have hD : 0 < (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ) := by
    exact_mod_cast markedRawCopiedProduct_pos ((markedRawActiveSplit pads) s.2.1).1
  have hd₀ : 0 ≤ d₀ := by linarith [hs.1.2]
  have hscale : ‖((d₀/(markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℝ):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg hd₀ hD.le)]
    exact (div_le_one hD).mpr hs.1.1
  have hsource := markedRawPendingDamping_norm_le s.2.2 s.1.1 (hZ _ s.1.2) hρ₀ hρ₁
  have htarget := markedRawPendingDamping_norm_le (markedRawEdgeTargetMemory hZ s choice)
    choice.target.1 (hZ _ choice.target.2) hρ₀ hρ₁
  have hse := markedRawEndpointFactor_norm_le hZ (by norm_num : (0:ℝ)≤1) le_rfl χ hχ s
  have hte := markedRawEndpointFactor_norm_le hZ (by norm_num : (0:ℝ)≤1) le_rfl χ hχ
    (markedRawEdgeTargetState hZ s choice)
  have hdiv : (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ) ∣
      markedMinorIntegerDet s.1.1 (markedRawEdgeTargetState hZ s choice).1.1 := hs.2.1
  unfold markedRawEdgeChoiceDetectorCoefficient
  dsimp only
  rw [ite_eq_left hs.1,ite_eq_left hdiv,ite_eq_right hs.2.2.1]
  simp only [norm_mul]
  calc
    _ ≤ 1*1*1*H*H*‖detector (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2)
        (markedRawLastProduct (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh))
        (markedMinorIntegerDet s.1.1 choice.target.1/
          (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ))‖*1*1 := by
      gcongr <;> first | assumption | exact hη _ | exact le_rfl
    _ = _ := by ring

theorem markedRawEdgeCrude_coefficient_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    {ρ H : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hη : ∀ t, ‖η t‖ ≤ H)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖ ≤ H^2*
      ‖markedBanEdgeKernel ψ Q Y (markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2)
        (markedRawLastProduct (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh))
        (markedMinorIntegerDet s.1.1 choice.target.1/
          (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ))‖ := by
  rw [markedRawEdgeChoiceCoefficient_detector]
  exact markedRawEdgeCrude_detector_norm_le hZ η d₀ Y hρ₀ hρ₁ hH hη χ hχ _ s choice

theorem markedRawEdgeCrude_coefficient_divides {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s)
    (hn : markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice ≠ 0) :
    (markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1:ℤ) ∣ markedMinorIntegerDet s.1.1 choice.target.1 := by
  rw [markedRawEdgeChoiceCoefficient_detector] at hn
  exact (markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ _ s choice hn).2.1

end ArtinMatthews
