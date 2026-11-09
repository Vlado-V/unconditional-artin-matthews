module

public import ArtinMatthews.SourceComparisonSquareErrorEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Assemble the original centered polynomial from the checked high-time
product bounds and its small-prime-square error. -/

namespace ArtinMatthews

open Finset MeasureTheory

noncomputable section

theorem sourceComparisonCentered_high_energy_of_branches {q : ℕ} [NeZero q] (h : ZMod q)
    (W β : ℕ → ℂ) (S : Finset ℕ) (ψ : ℝ → ℂ) (a b Y x ε σ T B X A : ℝ)
    (hx : 0 ≤ x) (hY : 0 < Y) (hX : 9 ≤ X) (hsupp : Function.support ψ ⊆ Set.Icc a b)
    (hS : ∀ p ∈ S, p.Prime) (hdis : Disjoint S (giantPrimeWindow x ε))
    (hinv : ∀ m ∈ giantPrimeWindow x ε, ∀ n, β (m*n) = β n)
    (hcap : ∀ n ∈ Ioc 0 ⌊b*Y⌋₊, (n:ℝ) ≤ (x^(1-ε))^2)
    (hV : ‖(bandReciprocalMass S:ℂ)⁻¹‖ ≤ X)
    (hCx : ‖(giantPrimeReciprocalSum x ε:ℂ)‖ ≤ 1)
    (hp : (∫ t in sourceComparisonHighTimes T B,
      ‖sourceComparisonProductMellin h S (giantPrimeWindow x ε)
        (Ioc 0 ⌊b*Y⌋₊) β ψ Y (t+σ)‖^2) ≤ X^(-(A+3)))
    (hc : (∫ t in sourceComparisonHighTimes T B,
      ‖sourceComparisonProductMellin h S {1} (Ioc 0 ⌊b*Y⌋₊) β ψ Y (t+σ)‖^2) ≤ X^(-(A+3)))
    (herr : (∫ t in sourceComparisonHighTimes T B,
      ‖sourceComparisonHighMellin h (fun n =>
        (W n-sourceComparisonRemovedWeight S β n)*(giantMarkedCenteredCore ε x n:ℂ)) ψ Y b (t+σ)‖^2) ≤
          X^(-A-1)) :
    (∫ t in sourceComparisonHighTimes T B,
      ‖sourceComparisonHighMellin h (fun n => W n*(giantMarkedCenteredCore ε x n:ℂ)) ψ Y b (t+σ)‖^2) ≤
        X^(-A) := by
  let I := sourceComparisonHighTimes T B
  let V : ℂ := (bandReciprocalMass S:ℂ)⁻¹
  let C : ℂ := giantPrimeReciprocalSum x ε
  let R := Ioc 0 ⌊b*Y⌋₊
  let P t := sourceComparisonProductMellin h S (giantPrimeWindow x ε) R β ψ Y (t+σ)
  let Q t := sourceComparisonProductMellin h S {1} R β ψ Y (t+σ)
  let E t := sourceComparisonHighMellin h (fun n =>
    (W n-sourceComparisonRemovedWeight S β n)*(giantMarkedCenteredCore ε x n:ℂ)) ψ Y b (t+σ)
  have hX0 : 0 < X := by linarith
  have hscale (z : ℂ) (hz : ‖z‖ ≤ X) (f : ℝ → ℂ)
      (hf : (∫ t in I, ‖f t‖^2) ≤ X^(-(A+3))) :
      (∫ t in I, ‖z*f t‖^2) ≤ X^(-A-1) := by
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ X^2*X^(-(A+3)) := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hz 2) hf (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_add hX0]
        congr 1
        ring
  have hVC : ‖-(V*C)‖ ≤ X := by
    rw [norm_neg, norm_mul]
    exact (mul_le_mul hV hCx (norm_nonneg _) hX0.le).trans_eq (mul_one _)
  let f : Fin 3 → ℝ → ℂ := ![E, fun t => V*P t, fun t => (-(V*C))*Q t]
  have hf₀ : f 0 = E := rfl
  have hf₁ : f 1 = fun t => V*P t := rfl
  have hf₂ : f 2 = fun t => (-(V*C))*Q t := rfl
  have hcont (j : Fin 3) : Continuous (f j) := by
    fin_cases j
    · change Continuous (f 0)
      rw [hf₀]
      exact (sourceComparisonHighMellin_continuous _ _ _ _ _).comp
        (continuous_id.add continuous_const)
    · change Continuous (f 1)
      rw [hf₁]
      exact continuous_const.mul ((sourceComparisonCutTriple_continuous _ _ _ _ _).comp
        (continuous_id.add continuous_const))
    · change Continuous (f 2)
      rw [hf₂]
      exact continuous_const.mul ((sourceComparisonCutTriple_continuous _ _ _ _ _).comp
        (continuous_id.add continuous_const))
  have he (j : Fin 3) : (∫ t in I, ‖f j t‖^2) ≤ X^(-A-1) := by
    fin_cases j
    · change (∫ t in I, ‖f 0 t‖^2) ≤ _
      simpa only [hf₀] using herr
    · change (∫ t in I, ‖f 1 t‖^2) ≤ _
      simpa only [hf₁] using hscale V hV P hp
    · change (∫ t in I, ‖f 2 t‖^2) ≤ _
      simpa only [hf₂] using hscale (-(V*C)) hVC Q hc
  have hsum := sourceComparison_finiteSum_energy (univ : Finset (Fin 3)) f
    (T := T) (W := I) (fun _ ht => ht.1) (fun j _ => hcont j) (fun j _ => he j)
  simp only [Fin.sum_univ_three, card_univ, Fintype.card_fin, Nat.cast_ofNat,
    hf₀, hf₁, hf₂] at hsum
  have hjoin (t : ℝ) :
      sourceComparisonHighMellin h (fun n => W n*(giantMarkedCenteredCore ε x n:ℂ)) ψ Y b (t+σ) =
        E t+V*P t+ (-(V*C))*Q t := by
    rw [sourceComparisonHighMellin_centered_eq h W β S ψ a b Y x ε (t+σ)
      hx hY hsupp hS hdis hinv hcap]
    change E t+V*(P t-C*Q t) = _
    ring
  simp_rw [hjoin]
  calc
    _ ≤ 9*X^(-A-1) := by simpa only [show (3:ℝ)^2=9 by norm_num] using hsum
    _ ≤ X*X^(-A-1) := mul_le_mul_of_nonneg_right hX (by positivity)
    _ = _ := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]
      congr 1
      ring

end
end ArtinMatthews
