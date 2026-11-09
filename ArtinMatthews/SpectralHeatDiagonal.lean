module

public import ArtinMatthews.SpectralHeatOrbitalKernel
public import ArtinMatthews.SpectralCuspHeightL2


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source-width cancellation and Gaussian KL Parseval for the
diagonal in the native heat trace. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

def spectralABLHeatDiagonal (H : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ t, H (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure

theorem spectralABLRegularHeat_inner (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R)
    (hF : MemLp (spectralKLHeatProfile R) 2 spectralKLPhysicalMeasure)
    (hG : MemLp (spectralABLRegularHeatProfile T ε R) 2 spectralKLPhysicalMeasure) :
    inner ℂ (hF.toLp _) (hG.toLp _) =
      spectralABLHeatDiagonal (spectralABLRegularCorrected T (T^(1-ε))) R := by
  rw [← spectralKLAnalysis.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralKLHeatProfile_completed_analysis R hR hF,
    spectralABLRegularHeatProfile_completed_analysis T ε R hT hR hG] with t htF htG
  rw [htF,htG,RCLike.inner_apply]
  change spectralKLGaussianWeightedData (spectralABLRegularCorrected T (T^(1-ε))) R (t : ℂ)*
    star (spectralKLGaussianData R (t : ℂ)) = _
  rw [spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralABLRegularCorrected T (T^(1-ε)) (t : ℂ)*
        (spectralKLGaussianData R (t : ℂ)*spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralABLExceptionalHeat_inner (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R)
    (hF : MemLp (spectralKLHeatProfile R) 2 spectralKLPhysicalMeasure)
    (hG : MemLp (spectralABLExceptionalHeatProfile a A R) 2 spectralKLPhysicalMeasure) :
    inner ℂ (hF.toLp _) (hG.toLp _) =
      spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A) R := by
  rw [← spectralKLAnalysis.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralKLHeatProfile_completed_analysis R hR hF,
    spectralABLExceptionalHeatProfile_completed_analysis a A R hA hR hG] with t htF htG
  rw [htF,htG,RCLike.inner_apply]
  change spectralKLGaussianWeightedData (spectralABLExceptionalCorrected a A) R (t : ℂ)*
    star (spectralKLGaussianData R (t : ℂ)) = _
  rw [spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralABLExceptionalCorrected a A (t : ℂ)*
        (spectralKLGaussianData R (t : ℂ)*spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]


theorem spectralABLRegularHeatDiagonal_integrable (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    Integrable (fun t : ℝ => spectralABLRegularCorrected T (T^(1-ε)) (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))
      spectralKLSpectralMeasure := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralABLRegularHeatProfile_properties T ε R hT hR).2.1
  have hi := L2.integrable_inner (𝕜 := ℂ)
    (spectralKLAnalysis (hF.toLp _)) (spectralKLAnalysis (hG.toLp _))
  apply hi.congr
  filter_upwards [spectralKLHeatProfile_completed_analysis R hR hF,
    spectralABLRegularHeatProfile_completed_analysis T ε R hT hR hG] with t htF htG
  rw [htF,htG,RCLike.inner_apply]
  change spectralKLGaussianWeightedData (spectralABLRegularCorrected T (T^(1-ε))) R (t : ℂ)*
    star (spectralKLGaussianData R (t : ℂ)) = _
  rw [spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralABLRegularCorrected T (T^(1-ε)) (t : ℂ)*
        (spectralKLGaussianData R (t : ℂ)*spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralABLExceptionalHeatDiagonal_integrable (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    Integrable (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))
      spectralKLSpectralMeasure := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralABLExceptionalHeatProfile_properties a A R hA hR).2.1
  have hi := L2.integrable_inner (𝕜 := ℂ)
    (spectralKLAnalysis (hF.toLp _)) (spectralKLAnalysis (hG.toLp _))
  apply hi.congr
  filter_upwards [spectralKLHeatProfile_completed_analysis R hR hF,
    spectralABLExceptionalHeatProfile_completed_analysis a A R hA hR hG] with t htF htG
  rw [htF,htG,RCLike.inner_apply]
  change spectralKLGaussianWeightedData (spectralABLExceptionalCorrected a A) R (t : ℂ)*
    star (spectralKLGaussianData R (t : ℂ)) = _
  rw [spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralABLExceptionalCorrected a A (t : ℂ)*
        (spectralKLGaussianData R (t : ℂ)*spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem gamma0HeatRegular_diagonal (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (n : ℤ) (hn : n ≠ 0) (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    (gamma0CuspTrueWidth N r : ℂ)*
      (cuspFourierHeightPairing
        (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
          (spectralKLHeatProfile R ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re)
        (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
          (spectralABLRegularHeatProfile T ε R ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) : ℂ) =
    spectralABLHeatDiagonal (spectralABLRegularCorrected T (T^(1-ε))) R := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralABLRegularHeatProfile_properties T ε R hT hR).2.1
  have hd := cuspFourierHeightPairing_dilation_inner |cuspFourierFrequency 1 n|
    (gamma0CuspTrueWidth N r : ℝ)
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) _ _ hF hG
    (fun x _ => spectralKLHeatProfile_real R x)
    (fun x _ => spectralABLRegularHeatProfile_real T ε R x)
  have hc : (((gamma0CuspTrueWidth N r : ℝ) : ℂ)) = (gamma0CuspTrueWidth N r : ℂ) := by norm_cast
  rw [hc] at hd
  exact hd.trans (spectralABLRegularHeat_inner T ε R hT hR hF hG)

theorem gamma0HeatExceptional_diagonal (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (n : ℤ) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    (gamma0CuspTrueWidth N r : ℂ)*
      (cuspFourierHeightPairing
        (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
          (spectralKLHeatProfile R ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re)
        (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
          (spectralABLExceptionalHeatProfile a A R ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) : ℂ) =
    spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A) R := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralABLExceptionalHeatProfile_properties a A R hA hR).2.1
  have hd := cuspFourierHeightPairing_dilation_inner |cuspFourierFrequency 1 n|
    (gamma0CuspTrueWidth N r : ℝ)
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) _ _ hF hG
    (fun x _ => spectralKLHeatProfile_real R x)
    (fun x _ => spectralABLExceptionalHeatProfile_real a A R x)
  have hc : (((gamma0CuspTrueWidth N r : ℝ) : ℂ)) = (gamma0CuspTrueWidth N r : ℂ) := by norm_cast
  rw [hc] at hd
  exact hd.trans (spectralABLExceptionalHeat_inner a A R hA hR hF hG)

end ArtinMatthews
