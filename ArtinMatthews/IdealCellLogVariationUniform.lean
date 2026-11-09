module

public import ArtinMatthews.IdealCellLogVariationActual


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed polynomial log-cell width controls the original slow phase
uniformly in the Mellin frequency and the rational remainder. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v

theorem idealCellLogVariation_uniform (a b c D : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Type u) (B : Type v)
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      ∀ (P : A → Finset ℕ) (R : B → Finset ℕ),
        (∀ i p, p ∈ P i → p.Prime) → (∀ i p, p ∈ R i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) → (∀ i, 0 < bandReciprocalMass (R i)) →
        ∀ (Q r : ℕ), (Q : ℝ) ≤ L^a → ∀ ξ : ℝ, 0 < ξ →
        ∀ (ζ β : ℝ) (u : ℤ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R),
          |ζ| ≤ L^c → |β| * (idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ) ≤ L^b →
          ‖idealCellLogVariation P R Q r (L^(-idealMajorCellExponent a b c D)) ξ ζ β u x y‖ ≤ L^(-D) := by
  let H := idealMajorCellExponent a b c D
  let K := 2*(1+2*Real.pi*Real.exp 2)
  have hH : 0 ≤ H := by dsimp [H, idealMajorCellExponent]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop (max 1 K)] with L hLlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hKL : K ≤ L := (le_max_right _ _).trans hLlarge
  have hh : 0 < L^(-H) := Real.rpow_pos_of_pos hL _
  have hh1 : L^(-H) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hH)
  intro A B _ _ _ _ P R hP hR hVP hVR Q r hQ ξ hξ ζ β u x y hζ hβ
  have hx : 0 < (idealSelectedProduct x : ℝ) := by exact_mod_cast idealSelectedProduct_pos hP x
  have hy : 0 < (idealSelectedProduct y : ℝ) := by exact_mod_cast idealSelectedProduct_pos hR y
  have hsum : |ζ| + 2*Real.pi * |β| * Real.exp (2*L^(-H))*(idealSelectedProduct x : ℝ)*
        (idealSelectedProduct y : ℝ) ≤ (1+2*Real.pi*Real.exp 2)*L^(b+c) := by
    have hza : |ζ| ≤ L^(b+c) := hζ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    have hba : L^b ≤ L^(b+c) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have he : Real.exp (2*L^(-H)) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have hp : |β| * Real.exp (2*L^(-H))*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ) ≤
        Real.exp 2*L^(b+c) := by
      calc
        _ = Real.exp (2*L^(-H))*(|β| * (idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ)) := by ring
        _ ≤ Real.exp 2*L^b := mul_le_mul he hβ (by positivity) (Real.exp_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hba (Real.exp_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
  have hQ4 : (Q : ℝ)^4 ≤ L^(4*a) := by
    calc
      _ ≤ (L^a)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 4
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; ring
  have hbound := idealCellLogVariation_bound P R hP hR hVP hVR Q r hh hξ ζ β u x y
  change ‖idealCellLogVariation P R Q r (L^(-H)) ξ ζ β u x y‖ ≤ _
  calc
    _ ≤ (Q : ℝ)^4 * (2*L^(-H)*(|ζ| + 2*Real.pi * |β| * Real.exp (2*L^(-H))*
        (idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ))) := hbound
    _ ≤ L^(4*a) * (2*L^(-H)*((1+2*Real.pi*Real.exp 2)*L^(b+c))) := by
      exact mul_le_mul hQ4 (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity) (by positivity)
    _ = K*L^(-D-4) := by
      have he : 4*a + -H + (b+c) = -D-4 := by dsimp [H, idealMajorCellExponent]; ring
      calc
        _ = K*(L^(4*a)*L^(-H)*L^(b+c)) := by dsimp [K]; ring
        _ = _ := by rw [← Real.rpow_add hL, ← Real.rpow_add hL, he]
    _ ≤ L*L^(-D-4) := mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hL.le _)
    _ = L^(-D-3) := by nth_rw 1 [← Real.rpow_one L]; rw [← Real.rpow_add hL]; congr 1; ring
    _ ≤ L^(-D) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

end
end ArtinMatthews
