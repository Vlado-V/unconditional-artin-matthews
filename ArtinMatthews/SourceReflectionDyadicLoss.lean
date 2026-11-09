module

public import ArtinMatthews.SourceReflectionDyadicScale


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit power losses for the retained and discarded Section 04 sums. -/
namespace ArtinMatthews.SourceEulerAssembly
noncomputable section

theorem sourceReflectionLossParameters {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ δ δ₁ δ₂ δ₃ : ℝ, 0 < δ ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ 0 < δ₃ ∧
      δ + 2 * M * δ₁ + (3 * M - 1 + δ) * δ₂ + δ₃ ≤ ε := by
  let δ := ε / 8
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hm : 0 < M := zero_lt_one.trans_le hM
  have hm' : 0 < 3 * M - 1 + δ := by linarith
  let δ₁ := ε / (16 * M)
  let δ₂ := ε / (8 * (3 * M - 1 + δ))
  have h₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have h₂ : 0 < δ₂ := by dsimp [δ₂]; positivity
  refine ⟨δ, δ₁, δ₂, δ, hd, h₁, h₂, hd, ?_⟩
  have h₁' : 2 * M * δ₁ = ε / 8 := by dsimp [δ₁]; field_simp; norm_num
  have h₂' : (3 * M - 1 + δ) * δ₂ = ε / 8 := by dsimp [δ₂]; field_simp
  rw [h₁', h₂']
  dsimp [δ]
  linarith

theorem sourceReflectionTailOrder {M δ δ₁ σ A : ℝ} (hM : 1 ≤ M)
    (hδ : 0 < δ) (hδ₁ : 0 ≤ δ₁) (hσ : 0 ≤ σ) (hA : 0 ≤ A) :
    ∃ N : ℝ, σ < N ∧
      A + 2 * M * δ₁ + 2 * σ * (2 * M - 1) < 2 * δ * (N - σ) := by
  let B := A + 2 * M * δ₁ + 2 * σ * (2 * M - 1)
  have hb : 0 ≤ B := by
    have : 0 ≤ 2 * M - 1 := by linarith
    dsimp [B]
    positivity
  refine ⟨σ + (B + 1) / (2 * δ), lt_add_of_pos_right _ (by positivity), ?_⟩
  change B < 2 * δ * (σ + (B + 1) / (2 * δ) - σ)
  have he : 2 * δ * (σ + (B + 1) / (2 * δ) - σ) = B + 1 := by field_simp; ring
  rw [he]
  exact lt_add_one _

theorem sourceReflectionLogPower_le {K m ε : ℝ} (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hε : 0 < ε) (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (Real.log (K * Z ^ m)) ^ n ≤ C * Z ^ ε := by
  let r := ε / (n : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hk : 0 < K := zero_lt_one.trans_le hK
  have hlogK := Real.log_nonneg hK
  let C := Real.log K + m / r + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C ^ n, pow_pos hC _, fun Z hZ => ?_⟩
  have hz := zero_lt_one.trans_le hZ
  have hz₁ := Real.one_le_rpow hZ hr.le
  have hs : Real.log (K * Z ^ m) ≤ C * Z ^ r := by
    rw [Real.log_mul hk.ne' (Real.rpow_pos_of_pos hz _).ne', Real.log_rpow hz]
    calc
      _ ≤ Real.log K * Z ^ r + m * (Z ^ r / r) :=
        add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz₁ hlogK)
          (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hz.le hr) hm)
      _ ≤ C * Z ^ r := by
        calc
          _ = (Real.log K + m / r) * Z ^ r := by ring
          _ ≤ C * Z ^ r := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
            (Real.rpow_nonneg hz.le _)
  have hKZ : 1 ≤ K * Z ^ m := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hZ hm)
  calc
    _ ≤ (C * Z ^ r) ^ n := pow_le_pow_left₀ (Real.log_nonneg hKZ) hs _
    _ = C ^ n * Z ^ ε := by
      rw [mul_pow, ← Real.rpow_natCast (Z ^ r) n, ← Real.rpow_mul hz.le]
      have he : r * (n : ℝ) = ε := by dsimp [r]; field_simp
      rw [he]

theorem sourceReflectionTailBudget {Z P D K M δ δ₁ N σ A : ℝ}
    (hZ : 1 ≤ Z) (hK : 1 ≤ K) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hPD : P * D ≤ K * Z ^ M) (hδ₁ : 0 ≤ δ₁) (hσ : 0 ≤ σ) (hN : σ ≤ N)
    (hloss : A + 2 * M * δ₁ + 2 * σ * (2 * M - 1) ≤ 2 * δ * (N - σ)) :
    Real.sqrt P * P ^ (2 * δ₁) * D * sourceReflectionLength Z P D ^ (2 * σ) *
      sourceReflectionTailScale Z P D δ ^ (-2 * (N - σ)) ≤
      (K ^ (2 * δ₁) * (8 * K ^ 2) ^ (2 * σ)) * Real.sqrt P * D * Z ^ (-A) := by
  have hz := zero_lt_one.trans_le hZ
  have hp := zero_le_one.trans hP
  have hd := zero_le_one.trans hD
  have hk := zero_le_one.trans hK
  have hL := sourceReflectionLength_pos hz (zero_lt_one.trans_le hP) (zero_lt_one.trans_le hD)
  have hJ : 0 < sourceReflectionTailScale Z P D δ :=
    (Real.rpow_pos_of_pos hz δ).trans_le (le_max_left _ _)
  have hP' : P ≤ K * Z ^ M := (by nlinarith only [hD, hp] : P ≤ P * D).trans hPD
  have hpw : P ^ (2 * δ₁) ≤ K ^ (2 * δ₁) * Z ^ (M * (2 * δ₁)) := by
    rw [Real.rpow_mul hz.le, ← Real.mul_rpow hk (Real.rpow_nonneg hz.le _)]
    exact Real.rpow_le_rpow hp hP' (by positivity)
  have hLw : sourceReflectionLength Z P D ^ (2 * σ) ≤
      (8 * K ^ 2) ^ (2 * σ) * Z ^ ((2 * M - 1) * (2 * σ)) := by
    rw [Real.rpow_mul hz.le, ← Real.mul_rpow (by positivity) (Real.rpow_nonneg hz.le _)]
    exact Real.rpow_le_rpow hL.le (sourceReflectionLength_le hZ hP hD hPD) (by positivity)
  have hJw : sourceReflectionTailScale Z P D δ ^ (-2 * (N - σ)) ≤
      Z ^ (δ * (-2 * (N - σ))) := by
    rw [Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hz _) (le_max_left _ _)
      (by linarith)
  calc
    _ ≤ Real.sqrt P * (K ^ (2 * δ₁) * Z ^ (M * (2 * δ₁))) * D *
        ((8 * K ^ 2) ^ (2 * σ) * Z ^ ((2 * M - 1) * (2 * σ))) *
          Z ^ (δ * (-2 * (N - σ))) := by
      gcongr
    _ = (K ^ (2 * δ₁) * (8 * K ^ 2) ^ (2 * σ)) * Real.sqrt P * D *
        Z ^ (M * (2 * δ₁) + (2 * M - 1) * (2 * σ) + δ * (-2 * (N - σ))) := by
      rw [Real.rpow_add hz, Real.rpow_add hz]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
      linarith

theorem sourceReflectionRetainedBudget {K M δ δ₁ δ₂ δ₃ ε : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hδ₃ : 0 < δ₃) (hloss : δ + 2 * M * δ₁ + (3 * M - 1 + δ) * δ₂ + δ₃ ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z P D : ℝ, 1 ≤ Z → 1 ≤ P → 1 ≤ D → P * D ≤ K * Z ^ M →
      1 ≤ sourceReflectionCutoff Z P D δ →
      Real.sqrt P * P ^ (2 * δ₁) * (Real.log (2 * sourceReflectionCutoff Z P D δ)) ^ 4 *
        (D + sourceReflectionCutoff Z P D δ) * (D * sourceReflectionCutoff Z P D δ) ^ δ₂ ≤
      C * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
  have hk := zero_le_one.trans hK
  have hk₂ : 1 ≤ 16 * K ^ 2 := by nlinarith only [hK, sq_nonneg (K - 1)]
  have hm : 0 ≤ 2 * M - 1 + δ := by linarith
  obtain ⟨C, hC, hc⟩ := sourceReflectionLogPower_le hk₂ hm hδ₃ 4 (by decide)
  refine ⟨8 * K ^ (2 * δ₁) * C * (8 * K ^ 3) ^ δ₂, by positivity, ?_⟩
  intro Z P D hZ hP hD hPD hR
  have hz := zero_lt_one.trans_le hZ
  have hp := zero_le_one.trans hP
  have hd := zero_le_one.trans hD
  have hP' : P ≤ K * Z ^ M := (by nlinarith only [hD, hp] : P ≤ P * D).trans hPD
  have hpw : P ^ (2 * δ₁) ≤ K ^ (2 * δ₁) * Z ^ (M * (2 * δ₁)) := by
    rw [Real.rpow_mul hz.le, ← Real.mul_rpow hk (Real.rpow_nonneg hz.le _)]
    exact Real.rpow_le_rpow hp hP' (by positivity)
  have hlog : (Real.log (2 * sourceReflectionCutoff Z P D δ)) ^ 4 ≤ C * Z ^ δ₃ := by
    have h₂R : 1 ≤ 2 * sourceReflectionCutoff Z P D δ := by linarith
    have hlog' := Real.log_le_log (zero_lt_one.trans_le h₂R)
      (show 2 * sourceReflectionCutoff Z P D δ ≤ 16 * K ^ 2 * Z ^ (2 * M - 1 + δ) by
        linarith only [sourceReflectionCutoff_le (δ := δ) hZ hP hD hPD])
    exact (pow_le_pow_left₀ (Real.log_nonneg h₂R) hlog' 4).trans (hc Z hZ)
  have hDr : (D * sourceReflectionCutoff Z P D δ) ^ δ₂ ≤
      (8 * K ^ 3) ^ δ₂ * Z ^ ((3 * M - 1 + δ) * δ₂) := by
    rw [Real.rpow_mul hz.le, ← Real.mul_rpow (by positivity) (Real.rpow_nonneg hz.le _)]
    exact Real.rpow_le_rpow (mul_nonneg hd (zero_le_one.trans hR))
      (sourceReflectionWeightedCutoff_le hZ hP hD hPD) hδ₂
  calc
    _ ≤ Real.sqrt P * (K ^ (2 * δ₁) * Z ^ (M * (2 * δ₁))) * (C * Z ^ δ₃) *
        (8 * Z ^ δ * (D + D ^ 2 * P / Z)) *
          ((8 * K ^ 3) ^ δ₂ * Z ^ ((3 * M - 1 + δ) * δ₂)) := by
      have hs := sourceReflectionSieveLength_le (P := P) hZ hδ hd
      gcongr
    _ = (8 * K ^ (2 * δ₁) * C * (8 * K ^ 3) ^ δ₂) *
        Z ^ (M * (2 * δ₁) + δ₃ + δ + (3 * M - 1 + δ) * δ₂) *
        Real.sqrt P * (D + D ^ 2 * P / Z) := by
      rw [Real.rpow_add hz, Real.rpow_add hz, Real.rpow_add hz]
      ring
    _ ≤ _ := by
      gcongr
      linarith

end
end ArtinMatthews.SourceEulerAssembly
