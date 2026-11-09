module

public import ArtinMatthews.SpectralHeatCuspidalSplit
public import ArtinMatthews.SpectralABLWindowPositivity


set_option backward.privateInPublic true
@[expose] public section

/-! Literal positivity on the actual principal energies follows from
the real source windows. Complementary values remain in the finite sum. -/

noncomputable section
open Set
namespace ArtinMatthews

theorem gamma0PrincipalCuspidalSymbol_norm_re_of_axis (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest)
    (hAxis : ∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ = (spectralContinuousTestSymbol h t).re)
    (i : Gamma0HeatPrincipalCuspidalIndex N) :
    ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re := by
  let l := gamma0AllHeightGradientSpectralValue N i.val
  let t := Real.sqrt (l-1/4)
  have ht : t^2 = l-1/4 := Real.sq_sqrt (sub_nonneg.mpr i.property)
  have he : spectralContinuousEnergyParameter t =
      ⟨l,gamma0AllHeightGradientSpectralValue_nonneg N i.val⟩ := by
    apply Subtype.ext
    change 1/4+t^2 = l
    rw [ht]
    ring
  unfold gamma0CuspidalTestSymbol
  change ‖h ⟨l,_⟩‖ = (h ⟨l,_⟩).re
  rw [← he]
  exact hAxis t

theorem spectralABLRegularEnergyTest_axis_positive (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    let h := spectralABLRegularEnergyTest T Δ hT hΔ
    (∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t) ∧
      (∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ = (spectralContinuousTestSymbol h t).re) := by
  dsimp only
  have he (t : ℝ) : spectralContinuousTestSymbol (spectralABLRegularEnergyTest T Δ hT hΔ) t =
      spectralABLRegularCorrected T Δ (t : ℂ) := by
    rw [spectralABLRegularEnergyTest_continuous_symbol,spectralABLRegularCorrected_real]
  constructor
  · intro t
    rw [he,spectralABLRegularCorrected_real,spectralABLRegularWindow_real,← Complex.ofReal_div,Complex.ofReal_re]
  · intro t
    rw [he,spectralABLRegularCorrected_norm_real,spectralABLRegularCorrected_real,
      spectralABLRegularWindow_real,← Complex.ofReal_div,Complex.ofReal_re]

theorem spectralABLExceptionalEnergyTest_axis_positive (a : ℝ) (A : ℕ) (hA : 1 ≤ A) :
    let h := spectralABLExceptionalEnergyTest a A hA
    (∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t) ∧
      (∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ = (spectralContinuousTestSymbol h t).re) := by
  dsimp only
  have he (t : ℝ) : spectralContinuousTestSymbol (spectralABLExceptionalEnergyTest a A hA) t =
      spectralABLExceptionalCorrected a A (t : ℂ) := by
    rw [spectralABLExceptionalEnergyTest_continuous_symbol,spectralABLExceptionalCorrected_real]
  constructor
  · intro t
    rw [he,spectralABLExceptionalCorrected_real,spectralABLExceptionalWindow_real,← Complex.ofReal_div,Complex.ofReal_re]
  · intro t
    rw [he,spectralABLExceptionalCorrected_norm_real,spectralABLExceptionalCorrected_real,
      spectralABLExceptionalWindow_real,← Complex.ofReal_div,Complex.ofReal_re]

end ArtinMatthews
