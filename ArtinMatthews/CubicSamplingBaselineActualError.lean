module

public import ArtinMatthews.CubicSamplingBaselineCauchy
public import ArtinMatthews.CubicSamplingSourceTail


set_option backward.privateInPublic true
@[expose] public section

/-! The actual discarded Section 6.3 marking layer saves every prescribed
logarithmic power after the divisor-fourth-moment Cauchy estimate. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators Topology

theorem giantCubicSampling_actualArray_baseline_error_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (hinj : Function.Injective e) (a : J → ℕ) (ha : ∀ j, 0 < a j)
    (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ∀ t, ‖Φ t‖ ≤ 1) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      let H (u : ℕ) : ℂ := ((∏ j, (bandWeight (P j) (V j) u) ^ a j : ℝ) : ℂ)
      let H₀ (u : ℕ) : ℂ := (cubicSamplingArrayTruncation P V a k u : ℂ)
      ∀ R : ℕ, (∑ r ∈ Finset.Icc 1 R,
        ‖giantCubicSamplingBaselineSum η χ H Φ x r -
          giantCubicSamplingBaselineSum η χ H₀ Φ x r‖) ≤ x * (Real.log x) ^ (-A) := by
  let C := 3 * (2 + Real.log 3) ^ 15
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have htrunc := cubicSampling_actualArray_retained_eventually e he hinj a ha zero_lt_one
  have htail := cubicSampling_actualArray_squareMean_log_saving e he hinj a ha (2 * A + 16)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 C))
  filter_upwards [htrunc, htail, hlog, eventually_gt_atTop (1 : ℝ)] with x hxtr hxe hxl hx₁
  dsimp only
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let L := Real.log x
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let H (u : ℕ) : ℂ := ((∏ j, (bandWeight (P j) (V j) u) ^ a j : ℝ) : ℂ)
  let H₀ (u : ℕ) : ℂ := (cubicSamplingArrayTruncation P V a k u : ℂ)
  let E := cubicSamplingArrayTail P V a (k + 1)
  have hL : 0 < L := Real.log_pos hx₁
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hxl
  have hLC : C ≤ L := (le_max_right _ _).trans hxl
  have hx : 0 ≤ x := zero_le_one.trans hx₁.le
  have hE (u : ℕ) (_hu : u ∈ U) : ‖H u - H₀ u‖ ≤ E u := by
    dsimp only [H, H₀]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hxtr.1 u
  intro R
  let S := ∑ r ∈ Finset.Icc 1 R,
    ‖giantCubicSamplingBaselineSum η χ H Φ x r -
      giantCubicSamplingBaselineSum η χ H₀ Φ x r‖
  have hSq : S ^ 2 ≤ (x * L ^ (-A)) ^ 2 := by
    have hp : L ^ (-(2 * A + 16)) * L ^ (15 : ℕ) =
        L ^ (-A) * L ^ (-A) * L⁻¹ := by
      calc
        _ = L ^ (-(2 * A + 16) + 15) := by
          rw [Real.rpow_add hL, show L ^ (15 : ℝ) = L ^ (15 : ℕ) from Real.rpow_natCast L 15]
        _ = L ^ ((-A) + (-A) + (-1)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_neg_one]
    calc
      _ ≤ (∑ u ∈ U, E u ^ 2) *
          (∑ u ∈ U, ((u + 1).divisors.card : ℝ) ^ 4) :=
        giantCubicSampling_baseline_error_square_le η χ H H₀ E Φ hΦ x R hE
      _ ≤ (x * L ^ (-(2 * A + 16))) * (C * x * L ^ (15 : ℕ)) :=
        mul_le_mul hxe (cubicSampling_shifted_divisor_fourth_log_bound hx₁.le hL₁)
          (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = (x * L ^ (-A)) ^ 2 * (C / L) := by
        calc
          _ = C * x ^ 2 * (L ^ (-(2 * A + 16)) * L ^ (15 : ℕ)) := by ring
          _ = _ := by rw [hp]; ring
      _ ≤ _ := mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hL).mpr hLC)
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg hx (Real.rpow_nonneg hL.le _))).mp hSq

end ArtinMatthews
