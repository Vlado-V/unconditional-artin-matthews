module

public import ArtinMatthews.SpectralBareDiagonalPositivity
public import ArtinMatthews.SpectralABLWindowLowerBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exceptional window is positive on the full energy axis,
and its bare diagonal controls the literal finite complementary moment. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralABLExceptionalEnergyTest_all_positive (a : ℝ) (ha : 0 < a)
    (A : ℕ) (hA : 1 ≤ A) (l : Ici (0 : ℝ)) :
    ((spectralABLExceptionalEnergyTest a A hA l).re : ℂ) =
      spectralABLExceptionalEnergyTest a A hA l ∧
      0 ≤ (spectralABLExceptionalEnergyTest a A hA l).re := by
  by_cases hl : (l : ℝ) ≤ 1/4
  · obtain ⟨c, hc, hlow⟩ := spectralABLExceptionalEnergyTest_re_lower_bound A hA
    exact ⟨spectralABLExceptionalEnergyTest_complementary_eq_real a A hA l hl,
      (mul_nonneg hc.le (Real.rpow_nonneg ha.le _)).trans (hlow a ha l hl)⟩
  · let t := Real.sqrt ((l : ℝ)-1/4)
    have hEq : spectralABLExceptionalEnergyTest a A hA l =
        ((spectralABLExceptionalWindowReal a A t/Real.cosh (Real.pi*t) : ℝ) : ℂ) := by
      rw [spectralABLExceptionalEnergyTest_apply,
        spectralSourceParameter_principal _ (le_of_not_ge hl),
        spectralABLExceptionalCorrected_real, spectralABLExceptionalWindow_real,
        Complex.ofReal_div]
    rw [hEq, Complex.ofReal_re]
    exact ⟨rfl, div_nonneg (spectralABLExceptionalWindowReal_nonneg a A t) (Real.cosh_pos _).le⟩

theorem gamma0ABLExceptional_cusp_finset_weighted_le (A : ℕ) (hA : 3 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
      (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
      (F : Finset (Gamma0AllHeightSpectralIndex N)),
      (∀ i ∈ F, gamma0AllHeightGradientSpectralValue N i ≤ 1/4) →
      ∀ (a : ℝ), 0 < a →
        c * (∑ i ∈ F, a^(-4*Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)) *
          ‖gamma0BareCuspidalAmplitude N i r Y hY n hn‖^2) ≤
        (gamma0BareSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
          r r Y hY n n hn hn).re := by
  have hA1 : 1 ≤ A := by omega
  obtain ⟨c, hc, hlow⟩ := spectralABLExceptionalEnergyTest_re_lower_bound A hA1
  refine ⟨c, hc, ?_⟩
  intro N inst r Y hY n hn F hF a ha
  let h := spectralABLExceptionalEnergyTest a A hA1
  have htrace := gamma0HeatExceptional_source_tendsto_bare N r r Y hY n n hn hn a A hA
  have hfin := gamma0BareSourceSpectralDiagonal_cusp_finset_le N h
    (fun l => (spectralABLExceptionalEnergyTest_all_positive a ha A hA1 l).1)
    (fun l => (spectralABLExceptionalEnergyTest_all_positive a ha A hA1 l).2)
    r Y hY n hn F htrace.1.of_norm htrace.2.1
  refine le_trans ?_ hfin
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_assoc]
  unfold gamma0BareCuspidalDiagonalDensity gamma0CuspidalTestSymbol
  exact mul_le_mul_of_nonneg_right
    (hlow a ha ⟨gamma0AllHeightGradientSpectralValue N i,
      gamma0AllHeightGradientSpectralValue_nonneg N i⟩ (hF i hi))
    (sq_nonneg _)

end ArtinMatthews
