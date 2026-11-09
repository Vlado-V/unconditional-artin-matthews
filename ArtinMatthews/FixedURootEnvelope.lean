module

public import OAI.NumberTheory.Jacobsthal.Estimates.SourcePairRemainder
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual incomplete-hyperbola error has the uniform polynomial envelope
used by the fixed-root residue count. The constant is independent of both moduli. -/

namespace ArtinMatthews
open OAI.Erdos970 ErdosHyperbolaError

/-- Absorb the genuine divisor and logarithmic factors of the rectangle error. -/
theorem fixedURootEnvelope_bound : ∃ C : ℝ, 0 < C ∧
    ∀ u S₁ : ℕ, 0 < u → 0 < S₁ →
      completionConstant*((u*S₁).divisors.card : ℝ)^3 *
        (Real.log (2*((u*S₁ : ℕ) : ℝ)))^2 *
        (((u*S₁ : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt S₁ ≤
          C * (u : ℝ)^(99/100 : ℝ) * (S₁ : ℝ)^2 := by
  obtain ⟨A,hA,hbound⟩ := ErdosHyperbolaWeighted.divisor_log_square_subpower 3
    (eps := (1/100 : ℝ)) (by norm_num)
  refine ⟨completionConstant*A, mul_pos completionConstant_pos hA, ?_⟩
  intro u S₁ hu hS₁
  have hCA : 0 < completionConstant*A := mul_pos completionConstant_pos hA
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hSR : (0 : ℝ) < S₁ := by exact_mod_cast hS₁
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hS1 : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁
  have huPow : (u : ℝ)^((1/100 : ℝ)+3/4) ≤ (u : ℝ)^(99/100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  have hSPow : (S₁ : ℝ)^(((1/100 : ℝ)+3/4)+1/2) ≤ (S₁ : ℝ)^2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hS1 (by norm_num)
  calc
    _ = completionConstant *
        (((u*S₁).divisors.card : ℝ)^3 * (Real.log (2*((u*S₁ : ℕ) : ℝ)))^2) *
          (((u*S₁ : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt S₁ := by ring
    _ ≤ completionConstant * (A * ((u*S₁ : ℕ) : ℝ)^(1/100 : ℝ)) *
          (((u*S₁ : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt S₁ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hbound (u*S₁) (Nat.mul_pos hu hS₁))
        completionConstant_pos.le
    _ = (completionConstant*A) * (u : ℝ)^((1/100 : ℝ)+3/4) *
          (S₁ : ℝ)^(((1/100 : ℝ)+3/4)+1/2) := by
      simp only [Nat.cast_mul, Real.mul_rpow huR.le hSR.le,
        Real.rpow_add huR, Real.rpow_add hSR, Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left huPow hCA.le) hSPow
      (by positivity) (mul_nonneg hCA.le (by positivity))


/-- Rectangle lengths at most `u` and `V` have the paper's fixed-`u` error.
There is one constant for every modulus, every residue, and every rectangle. -/
theorem fixedURootRectangleError_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (u S₁ S₂ : ℕ) (X Y : ℝ), 0 < u → 0 < S₁ → 0 < S₂ →
      0 ≤ X → X ≤ u → 0 ≤ Y →
      completionConstant*((u*S₁).divisors.card : ℝ)^3 *
        (Real.log (2*((u*S₁ : ℕ) : ℝ)))^2 *
        (((u*S₁ : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt S₁ *
        (1 + X/((u*S₁ : ℕ) : ℝ) + Y/((u*S₁ : ℕ) : ℝ)) ≤
      C * (u : ℝ)^(99/100 : ℝ) * ((S₁*S₂ : ℕ) : ℝ)^2 * (2 + Y/u) := by
  obtain ⟨C,hC,hbound⟩ := fixedURootEnvelope_bound
  refine ⟨C,hC,?_⟩
  intro u S₁ S₂ X Y hu h₁ h₂ hX hXu hY
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have h₁R : (1 : ℝ) ≤ S₁ := by exact_mod_cast h₁
  have h₂R : (1 : ℝ) ≤ S₂ := by exact_mod_cast h₂
  have hden : (u : ℝ) ≤ ((u*S₁ : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hdenpos : (0 : ℝ) < ((u*S₁ : ℕ) : ℝ) := huR.trans_le hden
  have hxf : X/((u*S₁ : ℕ) : ℝ) ≤ 1 := (div_le_one hdenpos).mpr (hXu.trans hden)
  have hyf : Y/((u*S₁ : ℕ) : ℝ) ≤ Y/u :=
    div_le_div_of_nonneg_left hY huR hden
  have hfac : 1 + X/((u*S₁ : ℕ) : ℝ) + Y/((u*S₁ : ℕ) : ℝ) ≤ 2+Y/u := by linarith
  have hmod : (S₁ : ℝ)^2 ≤ ((S₁*S₂ : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg ((S₂:ℝ)-1)]
  calc
    _ ≤ (C * (u : ℝ)^(99/100 : ℝ) * (S₁ : ℝ)^2) *
        (1 + X/((u*S₁ : ℕ) : ℝ) + Y/((u*S₁ : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (hbound u S₁ hu h₁) (by positivity)
    _ ≤ (C * (u : ℝ)^(99/100 : ℝ) * ((S₁*S₂ : ℕ) : ℝ)^2) * (2+Y/u) := by
      gcongr

end ArtinMatthews
