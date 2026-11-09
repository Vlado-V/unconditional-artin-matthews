module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-length descent used in the proof of Goldmakher–Louvel,
Theorem 4.3. The shorter column scales are exactly N / H^i. -/
namespace ArtinMatthews.QuadraticScale

noncomputable section

def descentColumn (N H : ℝ) (i : ℕ) : ℝ := N / H ^ i

theorem descentColumn_zero (N H : ℝ) : descentColumn N H 0 = N := by
  simp [descentColumn]

theorem descentColumn_succ (N H : ℝ) (i : ℕ) :
    descentColumn N H (i + 1) = descentColumn N H i / H := by
  rw [descentColumn, descentColumn, pow_succ, div_div]

theorem descentRatio_one_le {N : ℝ} (hN : 1 ≤ N) (r : ℕ) :
    1 ≤ N ^ (r : ℝ)⁻¹ :=
  Real.one_le_rpow hN (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem descentRatio_pow {N : ℝ} (hN : 0 ≤ N) {r : ℕ} (hr : 0 < r) :
    (N ^ (r : ℝ)⁻¹) ^ r = N := by
  rw [← Real.rpow_natCast, Real.rpow_inv_rpow hN (by exact_mod_cast hr.ne')]

theorem descentColumn_final {N : ℝ} (hN : 1 ≤ N) {r : ℕ} (hr : 0 < r) :
    descentColumn N (N ^ (r : ℝ)⁻¹) r = 1 := by
  rw [descentColumn, descentRatio_pow (zero_le_one.trans hN) hr,
    div_self (zero_lt_one.trans_le hN).ne']

theorem descentColumn_bounds {N : ℝ} (hN : 1 ≤ N) {r : ℕ} (hr : 0 < r)
    {i : ℕ} (hi : i ≤ r) :
    1 ≤ descentColumn N (N ^ (r : ℝ)⁻¹) i ∧
      descentColumn N (N ^ (r : ℝ)⁻¹) i ≤ N := by
  let H := N ^ (r : ℝ)⁻¹
  have hH : 1 ≤ H := descentRatio_one_le hN r
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hHi : 0 < H ^ i := pow_pos hH0 _
  change 1 ≤ N / H ^ i ∧ N / H ^ i ≤ N
  constructor
  · apply (le_div_iff₀ hHi).mpr
    rw [one_mul, ← descentRatio_pow (zero_le_one.trans hN) hr]
    exact pow_le_pow_right₀ hH hi
  · exact div_le_self (zero_le_one.trans hN) (one_le_pow₀ hH)

theorem descent_iterate (x : ℕ → ℝ) (r : ℕ) {A T : ℝ} (hA : 1 ≤ A)
    (hT : 0 ≤ T) (hbase : x r ≤ T) (hstep : ∀ i < r, x i ≤ A * (x (i + 1) + T)) :
    x 0 ≤ ((r : ℝ) + 1) * A ^ r * T := by
  have hrec (k : ℕ) (hk : k ≤ r) : x (r - k) ≤ ((k : ℝ) + 1) * A ^ k * T := by
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      have hk' : k ≤ r := by omega
      have hlt : r - (k + 1) < r := by omega
      have heq : r - (k + 1) + 1 = r - k := by omega
      have hT' : T ≤ A ^ k * T := le_mul_of_one_le_left hT (one_le_pow₀ hA)
      calc
        x (r - (k + 1)) ≤ A * (x (r - (k + 1) + 1) + T) := hstep _ hlt
        _ ≤ A * ((((k : ℝ) + 1) * A ^ k * T) + A ^ k * T) := by
          rw [heq]
          exact mul_le_mul_of_nonneg_left (add_le_add (ih hk') hT') (zero_le_one.trans hA)
        _ = _ := by push_cast; rw [pow_succ]; ring
  simpa only [Nat.sub_self] using hrec r le_rfl

theorem exists_descent_precision (a ε : ℝ) (ha : 1 < a) (hε : 0 < ε) :
    ∃ (r : ℕ) (δ : ℝ), 0 < r ∧ 0 < δ ∧
      δ * (a + 3 / 2) * (r : ℝ) + 5 / (r : ℝ) ≤ ε ∧
      δ * (2 * a - 1) ≤ ε / 2 := by
  obtain ⟨r, hr⟩ := exists_nat_gt (10 / ε)
  have hr0 : 0 < (r : ℝ) := (by positivity : 0 < 10 / ε).trans hr
  let δ := ε / (4 * (r : ℝ) * (a + 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have haux : δ * (4 * (r : ℝ) * (a + 2)) = ε := by dsimp [δ]; field_simp
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by exact_mod_cast hr0)
  have h₁ : δ * (a + 3 / 2) * (r : ℝ) ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_right (show a + 3 / 2 ≤ a + 2 by linarith)
      (mul_nonneg hδ.le hr0.le)
    nlinarith
  have h₂ : 5 / (r : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ hr0).mpr
    have h := (div_lt_iff₀ hε).mp hr
    nlinarith
  have h₃ : δ * (2 * a - 1) ≤ ε / 2 := by
    have h := mul_le_mul_of_nonneg_left (show 2 * a - 1 ≤ 2 * (a + 1) by linarith) hδ.le
    have hh := le_mul_of_one_le_left (show 0 ≤ δ * (2 * (a + 2)) by positivity) hr1
    nlinarith
  exact ⟨r, δ, by exact_mod_cast hr0, hδ, by linarith, h₃⟩

end
end ArtinMatthews.QuadraticScale
