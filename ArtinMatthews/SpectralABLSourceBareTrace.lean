module

public import ArtinMatthews.SpectralBareSpectrumLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The unregularized source trace for the two actual windows.
All cusp, continuous, and residual coefficients are retained. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology
namespace ArtinMatthews

private theorem spectralLimit_eq_of_heat_trace {S G : ℝ → ℂ} {s g : ℂ}
    (hS : Tendsto (fun k : ℕ => S ((k : ℝ)+1)) atTop (𝓝 s))
    (hG : Tendsto G atTop (𝓝 g)) (he : ∀ R : ℝ, 0 < R → S R = G R) :
    s = g := by
  apply tendsto_nhds_unique hS
  apply (hG.comp spectralHeatScale_nat_tendsto_atTop).congr'
  exact Eventually.of_forall (fun k => (he ((k : ℝ)+1) (by positivity)).symm)

theorem gamma0ABLRegular_sameCusp_bare_source_trace (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (T ε : ℝ) (hT : 0 < T) :
    let h := spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
    let H := spectralABLRegularCorrected T (T^(1-ε))
    gamma0BareSourceSpectralSide N h r r Y hY m n hm hn =
      (1/4 : ℂ)*((if m = n then spectralABLBareDiagonal H else 0)+
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r r c m n H) := by
  dsimp only
  have hS := (gamma0HeatRegular_source_tendsto_bare N r r Y hY m n hm hn T ε hT).2.2
  have hA' := (gamma0TrueWidthRegularHeatSeries_tendsto_bare N r r m n hm hn T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)).2
  have hd : Tendsto (fun R : ℝ => if m = n then spectralABLHeatDiagonal (spectralABLRegularCorrected T (T^(1-ε))) R else 0)
      atTop (𝓝 (if m = n then spectralABLBareDiagonal (spectralABLRegularCorrected T (T^(1-ε))) else 0)) := by
    by_cases hmn : m = n
    · simpa only [ite_eq_left hmn] using spectralABLRegularHeatDiagonal_tendsto T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
    · simpa only [ite_eq_right hmn] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  exact spectralLimit_eq_of_heat_trace hS (tendsto_const_nhds.mul (hd.add hA')) (fun R hR =>
    gamma0HeatRegular_sameCusp_source_trace N r Y hY m n hm hn T ε R hT hR)

theorem gamma0ABLRegular_inequivalent_bare_source_trace (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (T ε : ℝ) (hT : 0 < T) :
    let h := spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
    let H := spectralABLRegularCorrected T (T^(1-ε))
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r s c m n H) := by
  dsimp only
  have hS := (gamma0HeatRegular_source_tendsto_bare N r s Y hY m n hm hn T ε hT).2.2
  have hA' := (gamma0TrueWidthRegularHeatSeries_tendsto_bare N r s m n hm hn T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)).2
  exact spectralLimit_eq_of_heat_trace hS (tendsto_const_nhds.mul hA') (fun R hR =>
    gamma0HeatRegular_inequivalent_source_trace N r s hneq Y hY m n hm hn T ε R hT hR)

theorem gamma0ABLExceptional_sameCusp_bare_source_trace (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    let h := spectralABLExceptionalEnergyTest a A (by omega)
    let H := spectralABLExceptionalCorrected a A
    gamma0BareSourceSpectralSide N h r r Y hY m n hm hn =
      (1/4 : ℂ)*((if m = n then spectralABLBareDiagonal H else 0)+
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r r c m n H) := by
  dsimp only
  have hS := (gamma0HeatExceptional_source_tendsto_bare N r r Y hY m n hm hn a A hA).2.2
  have hA' := (gamma0TrueWidthExceptionalHeatSeries_tendsto_bare N r r m n hm hn a A hA).2
  have hd : Tendsto (fun R : ℝ => if m = n then spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A) R else 0)
      atTop (𝓝 (if m = n then spectralABLBareDiagonal (spectralABLExceptionalCorrected a A) else 0)) := by
    by_cases hmn : m = n
    · simpa only [ite_eq_left hmn] using spectralABLExceptionalHeatDiagonal_tendsto a A hA
    · simpa only [ite_eq_right hmn] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  exact spectralLimit_eq_of_heat_trace hS (tendsto_const_nhds.mul (hd.add hA')) (fun R hR =>
    gamma0HeatExceptional_sameCusp_source_trace N r Y hY m n hm hn a A R (by omega) hR)

theorem gamma0ABLExceptional_inequivalent_bare_source_trace (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    let h := spectralABLExceptionalEnergyTest a A (by omega)
    let H := spectralABLExceptionalCorrected a A
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r s c m n H) := by
  dsimp only
  have hS := (gamma0HeatExceptional_source_tendsto_bare N r s Y hY m n hm hn a A hA).2.2
  have hA' := (gamma0TrueWidthExceptionalHeatSeries_tendsto_bare N r s m n hm hn a A hA).2
  exact spectralLimit_eq_of_heat_trace hS (tendsto_const_nhds.mul hA') (fun R hR =>
    gamma0HeatExceptional_inequivalent_source_trace N r s hneq Y hY m n hm hn a A R (by omega) hR)

end ArtinMatthews
