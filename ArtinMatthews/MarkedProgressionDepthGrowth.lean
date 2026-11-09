module

public import ArtinMatthews.MarkedProgressionGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Subpolynomial retained mass at fixed multiples and shifts of the
logarithmic floor depth. This covers both `2*m` and `2*m+1` in the actual
Bonferroni truncation and its positive omitted tail. -/

namespace ArtinMatthews

open Filter
open scoped Topology

/-- A finite envelope for an arbitrary fixed multiple and shift of the
floor depth. -/
theorem marked_scaled_floor_truncation_exp_bound (t δ β : ℝ) (b J K : ℕ)
    (ht : 1 ≤ t) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) :
    ((b * ⌊t ^ δ⌋₊ + J + 1 : ℕ) : ℝ) *
        Real.exp (2 * ((b * ⌊t ^ δ⌋₊ + J + K : ℕ) : ℝ) * t ^ β) ≤
      Real.exp ((3 * (b : ℝ) + 3 * (J : ℝ) + 2 * (K : ℝ)) * t ^ (δ + β)) := by
  let n : ℕ := b * ⌊t ^ δ⌋₊ + J
  have ht0 : 0 < t := by linarith
  have hfloor : (⌊t ^ δ⌋₊ : ℝ) ≤ t ^ δ := Nat.floor_le (Real.rpow_nonneg ht0.le δ)
  have hn : (n : ℝ) ≤ (b : ℝ) * t ^ δ + J := by
    dsimp only [n]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg b)]
  have hlead : ((n + 1 : ℕ) : ℝ) ≤ Real.exp (n : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (n : ℝ)
  have hβ0 : 0 ≤ t ^ β := Real.rpow_nonneg ht0.le β
  have hδa : t ^ δ ≤ t ^ (δ + β) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hβa : t ^ β ≤ t ^ (δ + β) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have h1a : 1 ≤ t ^ (δ + β) := Real.one_le_rpow ht (by linarith)
  have hprod : t ^ (δ + β) = t ^ δ * t ^ β := Real.rpow_add ht0 δ β
  have hba := mul_le_mul_of_nonneg_left hδa (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have hJa := mul_le_mul_of_nonneg_left h1a (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  have hJKa := mul_le_mul_of_nonneg_left hβa
    (show (0 : ℝ) ≤ (J : ℝ) + K by positivity)
  have hexponent : (n : ℝ) + 2 * ((n + K : ℕ) : ℝ) * t ^ β ≤
      (3 * (b : ℝ) + 3 * (J : ℝ) + 2 * (K : ℝ)) * t ^ (δ + β) := by
    calc
      _ ≤ ((b : ℝ) * t ^ δ + J) + 2 * ((b : ℝ) * t ^ δ + J + K) * t ^ β := by
        have hnk : ((n + K : ℕ) : ℝ) = (n : ℝ) + (K : ℝ) := Nat.cast_add n K
        rw [hnk]
        nlinarith [mul_le_mul_of_nonneg_right hn hβ0]
      _ = (b : ℝ) * t ^ δ + J + 2 * (b : ℝ) * t ^ (δ + β) +
          2 * ((J : ℝ) + K) * t ^ β := by rw [hprod]; ring
      _ ≤ _ := by nlinarith
  change ((n + 1 : ℕ) : ℝ) * Real.exp (2 * ((n + K : ℕ) : ℝ) * t ^ β) ≤ _
  calc
    _ ≤ Real.exp (n : ℝ) * Real.exp (2 * ((n + K : ℕ) : ℝ) * t ^ β) :=
      mul_le_mul_of_nonneg_right hlead (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) + 2 * ((n + K : ℕ) : ℝ) * t ^ β) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- Fixed depth multipliers and shifts preserve subpolynomial retained mass. -/
theorem marked_scaled_truncation_mass_le_rpow_eventually (δ β : ℝ) (b J K : ℕ)
    (ε : ℝ) (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((b * ⌊(Real.log x) ^ δ⌋₊ + J + 1 : ℕ) : ℝ) *
          Real.exp (2 * ((b * ⌊(Real.log x) ^ δ⌋₊ + J + K : ℕ) : ℝ) * (Real.log x) ^ β) ≤
        x ^ ε := by
  filter_upwards [marked_sublinear_log_exp_le_rpow_eventually (δ + β)
      (3 * (b : ℝ) + 3 * (J : ℝ) + 2 * (K : ℝ)) ε hsum hε,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hlog
  exact (marked_scaled_floor_truncation_exp_bound (Real.log x) δ β b J K hlog hδ.le hβ.le).trans hx

/-- Natural-power form for the actual upper band endpoint. -/
theorem marked_scaled_truncation_power_le_rpow_eventually (δ β : ℝ) (b J K : ℕ)
    (ε : ℝ) (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((b * ⌊(Real.log x) ^ δ⌋₊ + J + 1 : ℕ) : ℝ) *
          (Real.exp (2 * (Real.log x) ^ β)) ^ (b * ⌊(Real.log x) ^ δ⌋₊ + J + K) ≤
        x ^ ε := by
  filter_upwards [marked_scaled_truncation_mass_le_rpow_eventually δ β b J K ε
    hδ hβ hsum hε] with x hx
  convert hx using 1
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The even Bonferroni truncation depth `2*floor((log x)^δ)`. -/
theorem marked_even_truncation_mass_le_rpow_eventually (δ β : ℝ) (K : ℕ)
    (ε : ℝ) (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((2 * ⌊(Real.log x) ^ δ⌋₊ + 1 : ℕ) : ℝ) *
          Real.exp (2 * ((2 * ⌊(Real.log x) ^ δ⌋₊ + K : ℕ) : ℝ) * (Real.log x) ^ β) ≤
        x ^ ε := by
  simpa only [Nat.add_zero] using
    marked_scaled_truncation_mass_le_rpow_eventually δ β 2 0 K ε hδ hβ hsum hε

/-- The first omitted layer at depth `2*floor((log x)^δ)+1`. -/
theorem marked_odd_tail_mass_le_rpow_eventually (δ β : ℝ) (K : ℕ)
    (ε : ℝ) (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((2 * ⌊(Real.log x) ^ δ⌋₊ + 1 + 1 : ℕ) : ℝ) *
          Real.exp (2 * ((2 * ⌊(Real.log x) ^ δ⌋₊ + 1 + K : ℕ) : ℝ) * (Real.log x) ^ β) ≤
        x ^ ε :=
  marked_scaled_truncation_mass_le_rpow_eventually δ β 2 1 K ε hδ hβ hsum hε

end ArtinMatthews
