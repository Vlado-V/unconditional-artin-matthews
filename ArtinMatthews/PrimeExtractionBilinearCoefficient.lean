module

public import ArtinMatthews.PrimeExtractionDirectReduction


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine coefficient matrix after extracting the first rough prime.
Its uniform bound includes the actual marking array, theta coefficients,
Dirichlet twist and factorial normalization. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators

theorem roughThetaFirstCoefficient_norm_le (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) (m : ℕ) :
    ‖roughPrimeFirstCoefficient (fun p => idealThetaCoeff η p * χ p) z m‖ ≤ 2 := by
  classical
  unfold roughPrimeFirstCoefficient
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (idealThetaCoeff_prime_norm_le_two η h.1) (χ.norm_le_one _)
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  · simp

theorem roughThetaTupleCoefficient_div_larger_factorial_norm_le
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (j n : ℕ) (z : ℝ) :
    ‖roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) (j - 1) n z /
      j.factorial‖ ≤ (2 : ℝ) ^ (j - 1) := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos j : (0 : ℝ) < j.factorial)).mpr
  calc
    _ ≤ ((j - 1).factorial : ℝ) * (2 : ℝ) ^ (j - 1) :=
      roughThetaTupleCoefficient_norm_le η χ _ _ _
    _ ≤ (j.factorial : ℝ) * (2 : ℝ) ^ (j - 1) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.factorial_le (Nat.sub_le _ _)))
        (by positivity)
    _ = _ := mul_comm _ _

noncomputable def markedExtractionBilinearCoefficient {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (γ : ℝ) (j : ℕ) (x : ℝ) (m n : ℕ) : ℂ :=
  (literalMarkedArrayWeight e x (m * n - 1) : ℂ) * G x (m * n - 1) *
    roughPrimeFirstCoefficient (fun p => idealThetaCoeff η p * χ p) (x ^ γ) m *
      (roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) (j - 1) n (x ^ γ) /
        j.factorial)

theorem markedExtractionBilinearCoefficient_bound {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (γ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᶠ x : ℝ in atTop, ∀ m n : ℕ,
      ‖markedExtractionBilinearCoefficient e η χ G γ j x m n‖ ≤
        (2 / Real.log 2) ^ Fintype.card ι * CG * (2 : ℝ) ^ j := by
  filter_upwards [literalMarkedArrayWeight_bound_eventually e he, hG] with x hW hGx
  intro m n
  have hw : ‖(literalMarkedArrayWeight e x (m * n - 1) : ℂ)‖ ≤
      (2 / Real.log 2) ^ Fintype.card ι := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (literalMarkedArrayWeight_nonneg e x (m * n - 1))] using hW _
  have hp := roughThetaFirstCoefficient_norm_le η χ (x ^ γ) m
  have hb := roughThetaTupleCoefficient_div_larger_factorial_norm_le η χ j n (x ^ γ)
  unfold markedExtractionBilinearCoefficient
  simp only [norm_mul]
  calc
    _ ≤ (2 / Real.log 2) ^ Fintype.card ι * CG * 2 * (2 : ℝ) ^ (j - 1) := by
      gcongr
      exact hGx _
    _ = _ := by
      rw [mul_assoc, mul_assoc, ← pow_succ', Nat.sub_add_cancel hj]
      ring

end ArtinMatthews
