module

public import ArtinMatthews.MarkedMajorMellinConstructed
public import ArtinMatthews.MarkedMajorFourierDecay
public import ArtinMatthews.MarkedMajorFourierWeightPlane


set_option backward.privateInPublic true
@[expose] public section

/-! Scaled rapid decay, mass and tails of the constructed actual major coefficient. -/
namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem markedMajorConstructedCoefficient_scaled_decay (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta : ℝ, ∀ p : ℝ × ℝ,
      ‖markedMajorConstructedCoefficient ψ ha hab hψ hX theta p‖ ≤
        C*markedMajorFourierPlaneWeight (1+|theta|) n p := by
  obtain ⟨C,hC,hD⟩ := markedMajorConstructedKernel_uniform_L1_bounds ψ ha hab hψ (2*n)
  refine ⟨markedMajorFourierDecayConstant n*C,
    mul_pos (markedMajorFourierDecayConstant_pos n) hC,fun X hX hXp theta p => ?_⟩
  have hW : 1 ≤ 1+|theta| := le_add_of_nonneg_right (abs_nonneg theta)
  have H := markedMajorFourierCoefficient_scaled_div
    (markedMajorConstructedKernel ψ ha hab hψ hXp theta) n hC.le hW
    (fun k hk => hD k hk X hX hXp theta) p
  convert H using 1
  · rfl
  · unfold markedMajorFourierPlaneWeight markedMajorFourierWeight
    ring

theorem markedMajorConstructedCoefficient_scaled_rpow (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta : ℝ, ∀ p : ℝ × ℝ,
      ‖markedMajorConstructedCoefficient ψ ha hab hψ hX theta p‖ ≤
        C*(1+|p.1|/(1+|theta|))^(-(n : ℝ))*(1+|p.2|/(1+|theta|))^(-(n : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := markedMajorConstructedCoefficient_scaled_decay ψ ha hab hψ n
  refine ⟨C,hC,fun X hX hXp theta p => ?_⟩
  convert hb X hX hXp theta p using 1
  rw [Real.rpow_neg (by positivity),Real.rpow_natCast,
    Real.rpow_neg (by positivity),Real.rpow_natCast]
  unfold markedMajorFourierPlaneWeight markedMajorFourierWeight
  ring

theorem markedMajorConstructedCoefficient_L1_bound (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta : ℝ,
      (∫ p : ℝ × ℝ, ‖markedMajorConstructedCoefficient ψ ha hab hψ hX theta p‖) ≤
        C*(1+|theta|)^2 := by
  obtain ⟨C,hC,hb⟩ := markedMajorConstructedCoefficient_scaled_decay ψ ha hab hψ 2
  refine ⟨C*markedMajorFourierWeightMass^2+1,by positivity,fun X hX hXp theta => ?_⟩
  have H := markedMajorFourier_coefficient_L1_bound
    (markedMajorConstructedCoefficient ψ ha hab hψ hXp theta) (by positivity : 0 < 1+|theta|)
    (hb X hX hXp theta)
  calc
    _ ≤ C*((1+|theta|)*markedMajorFourierWeightMass)^2 := H
    _ ≤ (C*markedMajorFourierWeightMass^2+1)*(1+|theta|)^2 := by nlinarith [sq_nonneg (1+|theta|)]

theorem markedMajorConstructedCoefficient_tail_bound (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta T : ℝ, 0 ≤ T →
      (∫ p : ℝ × ℝ in {p | T ≤ |p.1| ∨ T ≤ |p.2|},
        ‖markedMajorConstructedCoefficient ψ ha hab hψ hX theta p‖) ≤
        C*(1+|theta|)^2*((1+T/(1+|theta|))^n)⁻¹ := by
  obtain ⟨C,hC,hb⟩ := markedMajorConstructedCoefficient_scaled_decay ψ ha hab hψ (n+2)
  refine ⟨C*markedMajorFourierWeightMass^2+1,by positivity,fun X hX hXp theta T hT => ?_⟩
  have H := markedMajorFourier_coefficient_tail_bound
    (markedMajorConstructedCoefficient ψ ha hab hψ hXp theta) (by positivity : 0 < 1+|theta|)
    hT hC.le n (hb X hX hXp theta)
  have hn : 0 ≤ ((1+T/(1+|theta|))^n)⁻¹ := by positivity
  calc
    _ ≤ C*((1+T/(1+|theta|))^n)⁻¹*((1+|theta|)*markedMajorFourierWeightMass)^2 := H
    _ ≤ (C*markedMajorFourierWeightMass^2+1)*(1+|theta|)^2*((1+T/(1+|theta|))^n)⁻¹ := by
      nlinarith [mul_nonneg (sq_nonneg (1+|theta|)) hn]

end
end ArtinMatthews
