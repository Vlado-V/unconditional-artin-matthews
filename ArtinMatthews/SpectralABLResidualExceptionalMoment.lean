module

public import ArtinMatthews.SpectralABLExceptionalDiagonalLower
public import ArtinMatthews.SpectralABLExceptionalCompactDensity


set_option backward.privateInPublic true
@[expose] public section

/-! The positive exceptional bare diagonal controls the actual finite
residual cosine-weighted moment. A vanishing mode contributes zero at
every energy, including energy zero. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0ResidualCosineExceptionalMoment (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (a : ℝ) : ℝ :=
  ∑ l ∈ gamma0ResidualEnergyWindow N, ∑ j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)),
    let κ := Real.sqrt (1/4-(l : ℝ))
    let ρ := gamma0ResidualABLSourceRho N l j b n hn
    a^(-4*κ)*‖(Real.sqrt |(n : ℝ)| : ℂ)*ρ‖^2/Real.cos (Real.pi*κ)

theorem gamma0BareSourceSpectralDiagonal_residual_re_le (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (hr : ∀ l, ((h l).re : ℂ) = h l) (hp : ∀ l, 0 ≤ (h l).re)
    (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hC : Summable (gamma0BareCuspidalTerm N h b b Y hY n n hn hn))
    (hI : IntegrableOn (gamma0BareContinuousRhoIntegrand N h b b Y hY n n hn hn) (Ioi (0 : ℝ))) :
    (gamma0BareResidualRhoSum N h b b n n hn hn).re ≤
      (gamma0BareSourceSpectralSide N h b b Y hY n n hn hn).re := by
  have hC₀ : 0 ≤ (∑' i, gamma0BareCuspidalTerm N h b b Y hY n n hn hn i).re := by
    rw [Complex.re_tsum hC]
    apply tsum_nonneg
    intro i
    rw [gamma0BareCuspidalTerm_diagonal_re]
    exact mul_nonneg (hp _) (sq_nonneg _)
  have hI₀ := gamma0BareContinuousRhoIntegral_diagonal_re_nonneg N h hr hp b Y hY n hn hI
  unfold gamma0BareSourceSpectralSide
  rw [Complex.add_re,Complex.add_re]
  linarith

theorem spectral_cosine_complementary_lower_of_gap {l : ℝ} (hl : 3/16 ≤ l) :
    Real.cos (Real.pi/4) ≤ Real.cos (Real.pi*Real.sqrt (1/4-l)) := by
  have hk : Real.sqrt (1/4-l) ≤ 1/4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  rw [show Real.pi/4 = Real.pi*(1/4 : ℝ) by ring]
  exact mul_le_mul_of_nonneg_left hk Real.pi_pos.le

theorem gamma0ABLExceptional_residual_cosine_weighted_le (A : ℕ) (hA : 3 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0)
      (Y : ℝ) (hY : 0 < Y) (a : ℝ), 0 < a →
      (∀ (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))),
        gamma0ResidualABLSourceRho N l j b n hn ≠ 0 → 3/16 ≤ (l : ℝ)) →
      c*Real.cos (Real.pi/4)*gamma0ResidualCosineExceptionalMoment N b n hn a ≤
        (gamma0BareSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
          b b Y hY n n hn hn).re := by
  have hA₁ : 1 ≤ A := by omega
  obtain ⟨c,hc,hLower⟩ := spectralABLExceptionalEnergyTest_re_lower_bound A hA₁
  refine ⟨c,hc,?_⟩
  intro N inst b n hn Y hY a ha hgap
  let h := spectralABLExceptionalEnergyTest a A hA₁
  have hTrace := gamma0HeatExceptional_source_tendsto_bare N b b Y hY n n hn hn a A hA
  have hR := gamma0BareSourceSpectralDiagonal_residual_re_le N h
    (fun l => (spectralABLExceptionalEnergyTest_all_positive a ha A hA₁ l).1)
    (fun l => (spectralABLExceptionalEnergyTest_all_positive a ha A hA₁ l).2)
    b Y hY n hn hTrace.1.of_norm hTrace.2.1
  refine le_trans ?_ hR
  unfold gamma0ResidualCosineExceptionalMoment gamma0BareResidualRhoSum
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_le_sum
  intro j _
  let κ := Real.sqrt (1/4-(l : ℝ))
  let ρ := gamma0ResidualABLSourceRho N l j b n hn
  let W := (Real.sqrt |(n : ℝ)| : ℂ)*ρ
  let e := Real.cos (Real.pi/4)
  change c*e*(a^(-4*κ)*‖W‖^2/Real.cos (Real.pi*κ)) ≤ (h l*(W*star W)).re
  by_cases hρ : ρ = 0
  · simp [W,hρ]
  have hlq : (l : ℝ) ≤ 1/4 := ((mem_gamma0ResidualEnergyWindow N l).mp hl).1.2
  have he : 0 < e := by dsimp only [e]; rw [Real.cos_pi_div_four]; positivity
  have hCos : e ≤ Real.cos (Real.pi*κ) := spectral_cosine_complementary_lower_of_gap (hgap l j hρ)
  have hWeight : e*(a^(-4*κ)/Real.cos (Real.pi*κ)) ≤ a^(-4*κ) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (he.trans_le hCos)).mpr
    exact (mul_le_mul_of_nonneg_right hCos (Real.rpow_nonneg ha.le _)).trans_eq (mul_comm _ _)
  have hW : W*star W = ((‖W‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow,Complex.star_def] using Complex.mul_conj' W
  rw [hW,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ = (c*(e*(a^(-4*κ)/Real.cos (Real.pi*κ))))*‖W‖^2 := by ring
    _ ≤ (c*a^(-4*κ))*‖W‖^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWeight hc.le) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hLower a ha l hlq) (sq_nonneg _)

end ArtinMatthews
