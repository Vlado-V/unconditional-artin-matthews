module

public import ArtinMatthews.PrimeExtractionFactorCount
public import ArtinMatthews.GiantActualRoughSieve
public import ArtinMatthews.QuadraticIdealNormCountGlobal
public import Mathlib.NumberTheory.DirichletCharacter.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform bounds for the actual coefficients on the rough support. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators

/-- The actual marking array is globally bounded, uniformly in its integer
argument, once the fixed bands have reached their Mertens mass range. -/
theorem literalMarkedArrayWeight_bound_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) :
    ∀ᶠ x : ℝ in atTop, ∀ u : ℕ,
      literalMarkedArrayWeight e x u ≤ (2 / Real.log 2) ^ Fintype.card ι := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_all.mpr (fun i => marked_log_power_band_mass_eventually (he i))]
    with x hx
  intro u
  have hV (i : ι) : 0 < bandReciprocalMass (markedLogPowerBand (e i) x) := by
    exact lt_trans (by positivity : (0 : ℝ) < Real.log 2 / 2) (hx i).1
  calc
    _ ≤ ∏ i : ι, 1 / bandReciprocalMass (markedLogPowerBand (e i) x) :=
      divisorWeight_le Finset.univ _ (fun i _ => hV i) u
    _ ≤ ∏ _i : ι, 2 / Real.log 2 := by
      apply Finset.prod_le_prod₀ (fun i _ => div_nonneg zero_le_one (hV i).le)
      intro i _
      apply (div_le_div_iff₀ (hV i) hlog).mpr
      have := (hx i).1
      change Real.log 2 / 2 < bandReciprocalMass (markedLogPowerBand (e i) x) at this
      linarith
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

/-- The genuine Hecke theta coefficient, including any Dirichlet twist,
is bounded by the fixed rough-factor bound; no coefficient estimate is assumed. -/
theorem idealThetaCoeff_rough_bound_eventually (T : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ T * x →
      MarkedRoughAbove (x ^ γ) n → ∀ (η : HeckeFamily.Character) (q : ℕ)
      (χ : DirichletCharacter ℂ q),
      ‖idealThetaCoeff η n * χ n‖ ≤ (2 : ℝ) ^ ⌈2 / γ⌉₊ := by
  filter_upwards [marked_rough_factor_and_divisor_count_eventually T hγ] with x hx
  intro n hn hnT hnrough η q χ
  calc
    _ = ‖idealThetaCoeff η n‖ * ‖χ n‖ := norm_mul _ _
    _ ≤ (n.divisors.card : ℝ) * 1 := mul_le_mul
      (idealThetaCoeff_norm_le_divisors_card η n) (χ.norm_le_one _) (norm_nonneg _) (by positivity)
    _ ≤ _ := by simpa only [mul_one, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr (hx n hn hnT hnrough).2

end ArtinMatthews
