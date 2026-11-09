module

public import ArtinMatthews.SpectralHeatSpectralPairing
public import ArtinMatthews.SpectralNativeHeatGeometric
public import ArtinMatthews.SpectralHeatArithmeticKernel
public import ArtinMatthews.SpectralHeatDiagonal


set_option backward.privateInPublic true
@[expose] public section

/-! The full finite-Gaussian source trace. The literal J/K arithmetic
kernel, continuous density, residual spectrum, and quarter factor agree. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0HeatRegular_sameCusp_source_trace (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) r r Y hY m n hm hn R =
      (1/4 : ℂ)*((if m = n then spectralABLHeatDiagonal (spectralABLRegularCorrected T (T^(1-ε))) R else 0) +
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r r c m n (spectralABLRegularCorrected T (T^(1-ε))) R) := by
  have he := gamma0HeatRegular_sameCusp_geometric N r m n hm hn T ε R hT hR
  dsimp only at he
  unfold spectralABLLiteralRegularEnergyTest spectralABLRegularKuznetsovEnergyTest at he
  rw [gamma0HeatPoincareTest_source_pairing_eq N (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) r r Y hY m n hm hn R hR] at he
  have hseries : (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n
      (spectralABLRegularHeatProfile T ε R) (spectralKLHeatProfile R)) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r r c m n (spectralABLRegularCorrected T (T^(1-ε))) R :=
    tsum_congr (fun c => gamma0TrueWidthRegularHeatFibre N r r c m n hm hn T ε R hT hR)
  rw [hseries] at he
  by_cases hmn : m = n
  · subst n
    simpa only [ite_eq_left (rfl : m = m),gamma0HeatRegular_diagonal N r m hm T ε R hT hR] using he
  · simpa only [ite_eq_right hmn] using he

theorem gamma0HeatRegular_inequivalent_source_trace (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) r s Y hY m n hm hn R =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n (spectralABLRegularCorrected T (T^(1-ε))) R) := by
  have he := gamma0HeatRegular_inequivalent_geometric N r s hneq m n hm hn T ε R hT hR
  dsimp only at he
  unfold spectralABLLiteralRegularEnergyTest spectralABLRegularKuznetsovEnergyTest at he
  rw [gamma0HeatPoincareTest_source_pairing_eq N (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) r s Y hY m n hm hn R hR] at he
  have hseries : (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralABLRegularHeatProfile T ε R) (spectralKLHeatProfile R)) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n (spectralABLRegularCorrected T (T^(1-ε))) R :=
    tsum_congr (fun c => gamma0TrueWidthRegularHeatFibre N r s c m n hm hn T ε R hT hR)
  rw [hseries] at he
  exact he

theorem gamma0HeatExceptional_sameCusp_source_trace (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralABLExceptionalEnergyTest a A hA) r r Y hY m n hm hn R =
      (1/4 : ℂ)*((if m = n then spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A) R else 0) +
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r r c m n (spectralABLExceptionalCorrected a A) R) := by
  have he := gamma0HeatExceptional_sameCusp_geometric N r m n hm hn a A R hA hR
  dsimp only at he
  unfold spectralABLLiteralExceptionalEnergyTest spectralABLExceptionalKuznetsovEnergyTest at he
  rw [gamma0HeatPoincareTest_source_pairing_eq N (spectralABLExceptionalEnergyTest a A hA) r r Y hY m n hm hn R hR] at he
  have hseries : (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n
      (spectralABLExceptionalHeatProfile a A R) (spectralKLHeatProfile R)) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r r c m n (spectralABLExceptionalCorrected a A) R :=
    tsum_congr (fun c => gamma0TrueWidthExceptionalHeatFibre N r r c m n hm hn a A R hA hR)
  rw [hseries] at he
  by_cases hmn : m = n
  · subst n
    simpa only [ite_eq_left (rfl : m = m),gamma0HeatExceptional_diagonal N r m hm a A R hA hR] using he
  · simpa only [ite_eq_right hmn] using he

theorem gamma0HeatExceptional_inequivalent_source_trace (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralABLExceptionalEnergyTest a A hA) r s Y hY m n hm hn R =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n (spectralABLExceptionalCorrected a A) R) := by
  have he := gamma0HeatExceptional_inequivalent_geometric N r s hneq m n hm hn a A R hA hR
  dsimp only at he
  unfold spectralABLLiteralExceptionalEnergyTest spectralABLExceptionalKuznetsovEnergyTest at he
  rw [gamma0HeatPoincareTest_source_pairing_eq N (spectralABLExceptionalEnergyTest a A hA) r s Y hY m n hm hn R hR] at he
  have hseries : (∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralABLExceptionalHeatProfile a A R) (spectralKLHeatProfile R)) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n (spectralABLExceptionalCorrected a A) R :=
    tsum_congr (fun c => gamma0TrueWidthExceptionalHeatFibre N r s c m n hm hn a A R hA hR)
  rw [hseries] at he
  exact he

end ArtinMatthews
