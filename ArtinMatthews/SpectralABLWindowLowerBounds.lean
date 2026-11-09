module

public import ArtinMatthews.SpectralABLEnergyWindows


set_option backward.privateInPublic true
@[expose] public section

/-! Lower bounds for the actual corrected regular and complementary ABL
windows. The complementary identity uses the canceled Gamma factor through
the closed interval of orders. -/

namespace ArtinMatthews
open Set
open scoped BigOperators
noncomputable section

/-- The Gaussian centered at (T) alone gives the required lower bound
throughout the middle half of its width. -/
theorem spectralABLRegularCorrected_re_lower_bound (T Δ t : ℝ) (hT : 1 ≤ T)
    (hΔ : 0 < Δ) (hΔT : Δ ≤ T) (hw : |t - T| ≤ Δ / 2) :
    (Real.exp (-(1 / 4)) / 4) / Real.cosh (Real.pi * t) ≤
      (spectralABLRegularCorrected T Δ (t : ℂ)).re := by
  have ht : T / 2 ≤ t := by linarith [(abs_le.mp hw).1]
  have hTs : 0 < T ^ 2 := sq_pos_of_pos (by linarith)
  have hfac : 1 / 4 ≤ (t ^ 2 + 1 / 4) / T ^ 2 := by
    apply (le_div_iff₀ hTs).mpr
    nlinarith [pow_le_pow_left₀ (show 0 ≤ T / 2 by linarith) ht 2]
  have hlo : -(1 / 2 : ℝ) ≤ (t - T) / Δ :=
    (le_div_iff₀ hΔ).mpr (by linarith [(abs_le.mp hw).1])
  have hhi : (t - T) / Δ ≤ 1 / 2 :=
    (div_le_iff₀ hΔ).mpr (by linarith [(abs_le.mp hw).2])
  have hGaussian : Real.exp (-(1 / 4)) ≤ Real.exp (-(((t - T) / Δ) ^ 2)) := by
    have hpos : 0 ≤ 1 / 2 + (t - T) / Δ := by linarith
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hpos]
  rw [spectralABLRegularCorrected_real, spectralABLRegularWindow_real,
    ← Complex.ofReal_div, Complex.ofReal_re]
  apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
  unfold spectralABLRegularWindowReal
  calc
    _ = (1 / 4 : ℝ) * Real.exp (-(1 / 4)) := by ring
    _ ≤ _ := mul_le_mul hfac
      (hGaussian.trans (le_add_of_nonneg_right (Real.exp_nonneg _)))
      (Real.exp_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hfac)

/-- Exact real form of the corrected exceptional window at an imaginary
argument, including the removable half-order values. -/
theorem spectralABLExceptionalCorrected_imaginary_eq_real (a : ℝ) (A : ℕ) (κ : ℝ) :
    spectralABLExceptionalCorrected a A ((κ : ℂ) * Complex.I) =
      (((2 * Real.cosh (2 * κ * Real.log a)) ^ 2 /
          ((2 * (A : ℝ)) ^ 2 - κ ^ 2) ^ (2 * A) *
          (∏ k ∈ Finset.range A, ((((2 * (k + 1) + 1 : ℕ) : ℝ) / 2) ^ 2 - κ ^ 2)) *
          (Real.Gamma (3 / 2 - κ) * Real.Gamma (3 / 2 + κ) / Real.pi) : ℝ) : ℂ) := by
  let z : ℂ := (κ : ℂ) * Complex.I
  change spectralABLExceptionalCorrected a A z = _
  have hsq : z ^ 2 = ((-κ ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    push_cast
    linear_combination (κ : ℂ) ^ 2 * Complex.I_sq
  have hcos : Complex.cos (2 * z * (Real.log a : ℂ)) =
      (Real.cosh (2 * κ * Real.log a) : ℂ) := by
    rw [show 2 * z * (Real.log a : ℂ) = ((2 * κ * Real.log a : ℝ) : ℂ) * Complex.I by
      dsimp only [z]
      push_cast
      ring, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hden : z ^ 2 + (2 * (A : ℂ)) ^ 2 =
      (((2 * (A : ℝ)) ^ 2 - κ ^ 2 : ℝ) : ℂ) := by
    rw [hsq]
    push_cast
    ring
  have hprod :
      (∏ k ∈ Finset.range A, (z ^ 2 + (((2 * (k + 1) + 1 : ℕ) : ℂ) / 2) ^ 2)) =
        ((∏ k ∈ Finset.range A, ((((2 * (k + 1) + 1 : ℕ) : ℝ) / 2) ^ 2 - κ ^ 2) : ℝ) : ℂ) := by
    push_cast
    apply Finset.prod_congr rfl
    intro k _
    rw [hsq]
    push_cast
    ring
  have hminus : 3 / 2 + Complex.I * z = ((3 / 2 - κ : ℝ) : ℂ) := by
    dsimp only [z]
    push_cast
    linear_combination (κ : ℂ) * Complex.I_sq
  have hplus : 3 / 2 - Complex.I * z = ((3 / 2 + κ : ℝ) : ℂ) := by
    dsimp only [z]
    push_cast
    linear_combination -(κ : ℂ) * Complex.I_sq
  unfold spectralABLExceptionalCorrected spectralABLExceptionalBase spectralABLCoshCancellation
  rw [hcos, hden, hprod, hminus, hplus, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast <;> rfl

private theorem gamma_one_two_lower :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc (1 : ℝ) 2, m ≤ Real.Gamma x := by
  have hc : ContinuousOn Real.Gamma (Icc (1 : ℝ) 2) := by
    intro x hx
    exact (Real.differentiableAt_Gamma (fun n => by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨1, by norm_num⟩ hc
  exact ⟨Real.Gamma x, Real.Gamma_pos_of_pos (by linarith [hx.1]), isMinOn_iff.mp hmin⟩

private theorem exceptional_cosh_lower {a : ℝ} (ha : 0 < a) (κ : ℝ) :
    a ^ (-4 * κ) ≤ (2 * Real.cosh (2 * κ * Real.log a)) ^ 2 := by
  let u := 2 * κ * Real.log a
  have h : Real.exp (-u) ≤ 2 * Real.cosh u := by
    rw [Real.cosh_eq]
    linarith [Real.exp_nonneg u]
  calc
    _ = Real.exp (-u) ^ 2 := by
      rw [Real.rpow_def_of_pos ha, pow_two, ← Real.exp_add]
      congr 1
      dsimp only [u]
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) h 2

/-- The undivided corrected exceptional window dominates the source growth
weight throughout the closed complementary interval. -/
theorem spectralABLExceptionalCorrected_re_lower_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a κ : ℝ), 0 < a → 0 ≤ κ → κ ≤ 1 / 2 →
      c * a ^ (-4 * κ) ≤ (spectralABLExceptionalCorrected a A ((κ : ℂ) * Complex.I)).re := by
  obtain ⟨m, hm, hGamma⟩ := gamma_one_two_lower
  let D : ℝ := (2 * (A : ℝ)) ^ 2
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hA0 : (0 : ℝ) < A := by linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨(m ^ 2 / Real.pi) / D ^ (2 * A), by positivity, ?_⟩
  intro a κ ha hκ0 hκ1
  have hκsq : κ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hκ0 hκ1 2
  let d := D - κ ^ 2
  have hd : 0 < d := by
    dsimp only [d, D]
    nlinarith [pow_le_pow_left₀ zero_le_one hA1 2]
  have hden : d ^ (2 * A) ≤ D ^ (2 * A) :=
    pow_le_pow_left₀ hd.le (sub_le_self _ (sq_nonneg _)) _
  let U := (2 * Real.cosh (2 * κ * Real.log a)) ^ 2
  have hU : 0 ≤ U := sq_nonneg _
  have hquot : a ^ (-4 * κ) / D ^ (2 * A) ≤ U / d ^ (2 * A) :=
    (div_le_div_of_nonneg_right (exceptional_cosh_lower ha κ) (pow_nonneg hD.le _)).trans
      (div_le_div_of_nonneg_left hU (pow_pos hd _) hden)
  have hprod : 1 ≤ ∏ k ∈ Finset.range A, ((((2 * (k + 1) + 1 : ℕ) : ℝ) / 2) ^ 2 - κ ^ 2) := by
    apply Finset.one_le_prod₀
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    push_cast
    nlinarith [sq_nonneg (k : ℝ)]
  have hg₀ : m ≤ Real.Gamma (3 / 2 - κ) := hGamma _ ⟨by linarith, by linarith⟩
  have hg₁ : m ≤ Real.Gamma (3 / 2 + κ) := hGamma _ ⟨by linarith, by linarith⟩
  have hg : m ^ 2 / Real.pi ≤ Real.Gamma (3 / 2 - κ) * Real.Gamma (3 / 2 + κ) / Real.pi :=
    div_le_div_of_nonneg_right (by
      rw [pow_two]
      exact mul_le_mul hg₀ hg₁ hm.le (hm.le.trans hg₀)) Real.pi_pos.le
  rw [spectralABLExceptionalCorrected_imaginary_eq_real, Complex.ofReal_re]
  calc
    _ = (a ^ (-4 * κ) / D ^ (2 * A) * 1) * (m ^ 2 / Real.pi) := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul hquot hprod zero_le_one (div_nonneg hU (pow_nonneg hd.le _))) hg
      (by positivity) (mul_nonneg (div_nonneg hU (pow_nonneg hd.le _)) (zero_le_one.trans hprod))

private theorem spectralSourceParameter_complementary_of_le (l : ℝ) (hl : l ≤ 1 / 4) :
    spectralSourceParameter l = (Real.sqrt (1 / 4 - l) : ℂ) * Complex.I := by
  rw [spectralSourceParameter, Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hl),
    Complex.ofReal_zero, zero_add]

theorem spectralABLExceptionalEnergyTest_complementary_eq_real (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (l : Ici (0 : ℝ)) (hl : (l : ℝ) ≤ 1 / 4) :
    ((spectralABLExceptionalEnergyTest a A hA l).re : ℂ) =
      spectralABLExceptionalEnergyTest a A hA l := by
  rw [spectralABLExceptionalEnergyTest_apply, spectralSourceParameter_complementary_of_le _ hl,
    spectralABLExceptionalCorrected_imaginary_eq_real, Complex.ofReal_re]

theorem spectralABLExceptionalEnergyTest_re_lower_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ), 0 < a → ∀ l : Ici (0 : ℝ), (l : ℝ) ≤ 1 / 4 →
      c * a ^ (-4 * Real.sqrt (1 / 4 - l)) ≤ (spectralABLExceptionalEnergyTest a A hA l).re := by
  obtain ⟨c, hc, hlow⟩ := spectralABLExceptionalCorrected_re_lower_bound A hA
  refine ⟨c, hc, ?_⟩
  intro a ha l hl
  rw [spectralABLExceptionalEnergyTest_apply, spectralSourceParameter_complementary_of_le _ hl]
  apply hlow _ _ ha (Real.sqrt_nonneg _)
  calc
    _ ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt (sub_le_self _ l.property)
    _ = _ := by norm_num

end
end ArtinMatthews
