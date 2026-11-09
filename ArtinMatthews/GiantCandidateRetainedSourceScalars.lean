module

public import ArtinMatthews.GiantTwoSidedRootIntervalBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The source damping parameter and the reciprocal position factor
fit the literal dyad pairing with its external reciprocal scale. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem giantSignedSourceRho_exists {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ Real.sqrt q < ρ^2 := by
  let s := Real.sqrt (Real.sqrt q)
  let ρ := (s+1)/2
  have h₁ : Real.sqrt q < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hq hq1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (Real.sqrt_nonneg q) h₁
  have hρ : 0 < ρ := by unfold ρ; linarith
  have hsr : s < ρ := by unfold ρ; linarith
  refine ⟨ρ,hρ,by unfold ρ; linarith,?_⟩
  rw [← Real.sq_sqrt (Real.sqrt_nonneg q)]
  change s^2 < ρ^2
  nlinarith only [mul_pos (sub_pos.mpr hsr) (add_pos_of_nonneg_of_pos hs0 hρ)]

theorem giantTwoSidedRootInterval_reciprocal_norm_le_one {X : ℝ} (hX : 0 < X)
    {r : ℕ} (hr : r ∈ giantTwoSidedRootInterval X) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖((X : ℂ)/(r : ℂ))*u‖ ≤ 1 := by
  have h : X ≤ (r : ℝ) := (giantTwoSidedRootInterval_bounds hr).1
  have hr0 : 0 < (r : ℝ) := hX.trans_le h
  rw [norm_mul,norm_div, ← Complex.ofReal_natCast, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hX.le, Real.norm_of_nonneg hr0.le]
  exact (mul_le_of_le_one_right (div_nonneg hX.le hr0.le) hu).trans ((div_le_one hr0).mpr h)

theorem giantCandidateRetainedSourcePairing_normalized_log_saving (j : ℕ) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, let L := Real.log x
      let E := max A 0 + ((j*j:ℕ):ℝ)+2
      ∀ X : ℝ, 0 < X → ∀ z : ℂ,
        ‖z‖ ≤ 8*X*L^(-(E+1)+((j*j:ℕ):ℝ)+2) → ‖z/(X:ℂ)‖ ≤ L^(-A) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ)] with x hL
  intro L E X hX z hz
  have hL1 : 1 ≤ L := (by norm_num : (1:ℝ) ≤ 8).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have he : -(E+1)+((j*j:ℕ):ℝ)+2 = -max A 0 + -1 := by unfold E; ring
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hX.le]
  calc
    _ ≤ (8*X*L^(-(E+1)+((j*j:ℕ):ℝ)+2))/X := div_le_div_of_nonneg_right hz hX.le
    _ = (8/L)*L^(-max A 0) := by
      rw [he,Real.rpow_add hL0,Real.rpow_neg_one]
      field_simp
    _ ≤ L^(-max A 0) := mul_le_of_le_one_left (Real.rpow_nonneg hL0.le _) ((div_le_one hL0).mpr hL)
    _ ≤ L^(-A) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (le_max_left _ _))

end
end ArtinMatthews
