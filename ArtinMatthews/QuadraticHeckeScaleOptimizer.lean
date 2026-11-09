module

public import ArtinMatthews.QuadraticHeckeSieveBootstrap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The scale optimization in Goldmakher–Louvel, Theorem 4.1.
A fixed power of the logarithm in the enlargement threshold gives the
same exponent map. The Poisson estimate from Theorem 4.3 remains an
explicit, separately stated input. -/
namespace ArtinMatthews

noncomputable section

def QuadraticHeckePoissonScaleBound (energy : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    energy M N ≤ C * (M * N) ^ ε * (M + N + N ^ (2 * a - 1) * M ^ (1 - a))

private theorem quadraticScale_log_power_le (A : ℝ) (hA : 1 ≤ A) (k : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → A * (1 + Real.log T) ^ k ≤ C * T ^ δ := by
  let r : ℝ := δ / ((k : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  let C : ℝ := A * (1 + r⁻¹) ^ k
  refine ⟨C, by dsimp [C]; positivity [hA, hr], ?_⟩
  intro T hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : 1 ≤ T ^ r := Real.one_le_rpow hT hr.le
  have hlog : 1 + Real.log T ≤ (1 + r⁻¹) * T ^ r := by
    have h := Real.log_le_rpow_div hT0.le hr
    rw [div_eq_mul_inv] at h
    linarith
  have hnon : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have hrk : r * (k : ℝ) ≤ δ := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
    nlinarith
  calc
    _ ≤ A * ((1 + r⁻¹) * T ^ r) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hlog k) (by linarith)
    _ = C * T ^ (r * (k : ℝ)) := by
      rw [mul_pow, Real.rpow_mul_natCast hT0.le, ← mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hrk) (by positivity [C])

theorem quadraticHeckeSieveExponentBound_of_poisson_scale
    (energy : ℝ → ℝ → ℝ) {a : ℝ} (ha : 1 < a) (A : ℝ) (hA : 1 ≤ A) (k : ℕ)
    (henlarge : ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
      A * (1 + Real.log (M * N)) ^ k * M ≤ L →
      energy M N ≤ 16 * energy L N)
    (hpoisson : QuadraticHeckePoissonScaleBound energy a) :
    QuadraticHeckeSieveExponentBound energy (2 - a⁻¹) := by
  intro ε hε
  let η : ℝ := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hbound⟩ := hpoisson η hη
  obtain ⟨D, hD, hD1⟩ := quadraticScale_log_power_le A hA k (δ := 1) zero_lt_one
  obtain ⟨P, hP, hP1⟩ := quadraticScale_log_power_le A hA k (δ := ε / 2) (half_pos hε)
  refine ⟨48 * C * D ^ η * P, by positivity, ?_⟩
  intro M N hM hN
  let T := M * N
  let b : ℝ := 2 - a⁻¹
  let Y := max M (N ^ b)
  let F := A * (1 + Real.log T) ^ k
  let L := F * Y
  have ha0 : 0 < a := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hM hN
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hb1 : 1 ≤ b := by
    dsimp [b]
    have h := (inv_le_one₀ ha0).mpr ha.le
    linarith
  have hb2 : b ≤ 2 := by dsimp [b]; linarith [inv_pos.mpr ha0]
  have hMY : M ≤ Y := le_max_left _ _
  have hNY : N ^ b ≤ Y := le_max_right _ _
  have hY : 1 ≤ Y := hM.trans hMY
  have hF : 1 ≤ F :=
    one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by linarith [Real.log_nonneg hT]))
  have hYL : Y ≤ L := le_mul_of_one_le_left (zero_le_one.trans hY) hF
  have hL : 1 ≤ L := hY.trans hYL
  have hML : F * M ≤ L := mul_le_mul_of_nonneg_left hMY (zero_le_one.trans hF)
  have hF1 : F ≤ D * T := by simpa only [Real.rpow_one] using hD1 T hT
  have hFP : F ≤ P * T ^ (ε / 2) := hP1 T hT
  have hNT : N ≤ T := le_mul_of_one_le_left hN0.le hM
  have hMT : M ≤ T := le_mul_of_one_le_right (zero_le_one.trans hM) hN
  have hYupper : Y ≤ T ^ (2 : ℕ) := by
    apply max_le
    · exact hMT.trans (by nlinarith [sq_nonneg (T - 1)])
    · have h := (Real.rpow_le_rpow_of_exponent_le hN hb2).trans
          (Real.rpow_le_rpow hN0.le hNT (by norm_num : (0 : ℝ) ≤ 2))
      simpa only [Real.rpow_two] using h
  have hLN : L * N ≤ D * T ^ (4 : ℕ) := by
    calc
      L * N ≤ (D * T * T ^ (2 : ℕ)) * T := by
        apply mul_le_mul _ hNT hN0.le (by positivity)
        exact mul_le_mul hF1 hYupper (zero_le_one.trans hY) (by positivity)
      _ = _ := by ring
  have hpower : (L * N) ^ η ≤ D ^ η * T ^ (ε / 2) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ L * N) hLN hη.le
    rw [Real.mul_rpow hD.le (by positivity : 0 ≤ T ^ (4 : ℕ)),
      ← Real.rpow_natCast T 4, ← Real.rpow_mul hT0.le] at h
    have he : (4 : ℝ) * η = ε / 2 := by dsimp [η]; ring
    simpa only [Nat.cast_ofNat, he] using h
  have hdual : N ^ (2 * a - 1) * L ^ (1 - a) ≤ N ^ b := by
    calc
      _ ≤ N ^ (2 * a - 1) * (N ^ b) ^ (1 - a) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN0.le _)
        exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 b)
          (hNY.trans hYL) (by linarith)
      _ = N ^ (2 * a - 1 + b * (1 - a)) := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      _ = N ^ b := by
        congr 1
        dsimp [b]
        field_simp
        ring
  have hNle : N ≤ N ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hb1
  have hterms : L + N + N ^ (2 * a - 1) * L ^ (1 - a) ≤ 3 * F * Y := by
    have hYF : Y ≤ F * Y := hYL
    change F * Y + N + _ ≤ _
    linarith [hNle.trans hNY, hdual.trans hNY]
  have hYsum : Y ≤ M + N ^ b :=
    max_le (le_add_of_nonneg_right (Real.rpow_nonneg hN0.le _))
      (le_add_of_nonneg_left (zero_le_one.trans hM))
  have hTmul : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by
    rw [← Real.rpow_add hT0, add_halves]
  calc
    energy M N ≤ 16 * energy L N := henlarge M N L hM hN hML
    _ ≤ 16 * (C * (L * N) ^ η * (L + N + N ^ (2 * a - 1) * L ^ (1 - a))) :=
      mul_le_mul_of_nonneg_left (hbound L N hL hN) (by norm_num)
    _ ≤ 16 * (C * (D ^ η * T ^ (ε / 2)) * (3 * (P * T ^ (ε / 2)) * (M + N ^ b))) := by
      have hterms' := hterms.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left hFP (by norm_num : (0 : ℝ) ≤ 3))
        hYsum (zero_le_one.trans hY) (by positivity))
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hpower hC.le) hterms'
          (by positivity) (by positivity)) (by norm_num)
    _ = _ := by
      rw [← hTmul]
      ring

theorem quadraticHeckeSieveExponentBound_bootstrap_of_poisson_scale
    (energy : ℝ → ℝ → ℝ) (hbase : QuadraticHeckeSieveExponentBound energy 2)
    (A : ℝ) (hA : 1 ≤ A) (k : ℕ)
    (henlarge : ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
      A * (1 + Real.log (M * N)) ^ k * M ≤ L → energy M N ≤ 16 * energy L N)
    (hpoisson : ∀ a : ℝ, 1 < a → QuadraticHeckeSieveExponentBound energy a →
      QuadraticHeckePoissonScaleBound energy a) :
    QuadraticHeckeSieveExponentBound energy 1 :=
  quadraticHeckeSieveExponentBound_bootstrap energy hbase fun a ha hb =>
    quadraticHeckeSieveExponentBound_of_poisson_scale energy ha A hA k henlarge (hpoisson a ha hb)

end
end ArtinMatthews
