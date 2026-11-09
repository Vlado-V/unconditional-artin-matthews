module

public import ArtinMatthews.SourceComparisonCenteredProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Ordinary mean square for the actual small-prime-square coefficient error. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

theorem sourceComparisonHighMellin_square_error (ψ : ℝ → ℂ) {a b : ℝ}
    (hb : 0 ≤ b) (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : Continuous ψ)
    (A : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (Y T B σ : ℝ), 0 < Y → 0 < T → T ≤ X*Y →
      ∀ (q : ℕ) [NeZero q] (h : ZMod q) (E : ℕ → ℂ),
        (∑ n ∈ Ioc 0 ⌊b*Y⌋₊, ‖E n‖^2) ≤ (⌊b*Y⌋₊:ℝ)*X^(-(A+3)) →
        (∫ t in sourceComparisonHighTimes T B,
          ‖sourceComparisonHighMellin h E ψ Y b (t+σ)‖^2) ≤ X^(-A-1) := by
  have hcompact : HasCompactSupport ψ := by
    apply HasCompactSupport.intro' isCompact_Icc isClosed_Icc
    exact fun x hx => not_ne_iff.mp (fun h => hx (hsupp h))
  obtain ⟨y,hy⟩ := hψ.norm.exists_forall_ge_of_hasCompactSupport hcompact.norm
  let M := ‖ψ y‖
  let K := 8*Real.exp 1*(1+b)*b*M^2
  filter_upwards [eventually_ge_atTop (max 1 K)] with X hX
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hKX : K ≤ X := (le_max_right _ _).trans hX
  intro Y T B σ hY hT hTX q _ h E hE
  let N := ⌊b*Y⌋₊
  let c (n : ℕ) := E n*ψ ((n:ℝ)/Y)*ZMod.stdAddChar (h*(n:ZMod q))/Y
  have hN : (N:ℝ) ≤ b*Y := Nat.floor_le (mul_nonneg hb hY.le)
  have hmass : (∑ n ∈ Ioc 0 N, ‖c n‖^2) ≤ (M/Y)^2*((N:ℝ)*X^(-(A+3))) := by
    have hpoint (n : ℕ) : ‖c n‖ ≤ (M/Y)*‖E n‖ := by
      simp only [c, norm_div, norm_mul, giant_stdAddChar_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
      calc
        _ ≤ ‖E n‖*M/Y := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hy _) (norm_nonneg _)) hY.le
        _ = _ := by ring
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, ((M/Y)*‖E n‖)^2 :=
        sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint n) 2
      _ = (M/Y)^2*∑ n ∈ Ioc 0 N, ‖E n‖^2 := by simp only [mul_pow, mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)
  have hm := markedNaturalPolynomial_translated_mean_square (Ioc 0 N) Subset.rfl c σ hT
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at hm
  simp_rw [sourceComparisonHighMellin_eq_polynomial]
  have hcont : Continuous (fun t => markedNaturalPolynomial (Ioc 0 N) c (t+σ)) :=
    (markedNaturalPolynomial_continuous _ _).comp (continuous_id.add continuous_const)
  calc
    _ ≤ ∫ t in Set.Icc (-T) T, ‖markedNaturalPolynomial (Ioc 0 N) c (t+σ)‖^2 :=
      setIntegral_mono_set (hcont.norm.pow 2).integrableOn_Icc
        (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall (fun _ ht => ht.1))
    _ ≤ 8*Real.exp 1*(T+(N:ℝ))*((M/Y)^2*((N:ℝ)*X^(-(A+3)))) :=
      hm.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ ≤ 8*Real.exp 1*(((1+b)*X)*Y)*((M/Y)^2*((b*Y)*X^(-(A+3)))) := by
      have hh : T+(N:ℝ) ≤ ((1+b)*X)*Y := by
        have h₁ := add_le_add hTX hN
        have h₂ := mul_le_mul_of_nonneg_right hX1 hb
        have h₃ := mul_le_mul_of_nonneg_right h₂ hY.le
        nlinarith only [h₁,h₃]
      gcongr
    _ = K*X^(-A-2) := by
      have hpow : X*X^(-(A+3))=X^(-A-2) := by
        conv_lhs => lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_add hX0]
        congr 1
        ring
      dsimp [K]
      rw [← hpow]
      field_simp
    _ ≤ X*X^(-A-2) := mul_le_mul_of_nonneg_right hKX (by positivity)
    _ = _ := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]
      congr 1
      ring

end
end ArtinMatthews
