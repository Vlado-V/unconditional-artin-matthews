module

public import ArtinMatthews.SpectralHeatOrbitalKernel
public import ArtinMatthews.SpectralTrueWidthTwoProfileLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Gaussian-regularized J/K kernel in each actual
true-width arithmetic fibre. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def spectralABLHeatKernel (H : ℂ → ℂ) (R : ℝ) (m n : ℤ) (X : ℝ) : ℂ :=
  ∫ t, spectralWeylIntegerSignMultiplier m n t X*H (t : ℂ)*
    Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure


theorem spectralWeylIntegerSignMultiplier_bounded_positive (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖spectralWeylIntegerSignMultiplier m n t X‖ ≤ C := by
  by_cases hmn : 0 < m*n
  · simpa only [spectralWeylIntegerSignMultiplier,ite_eq_left hmn] using
      spectralWeylJMultiplier_bounded_positive hX
  · simpa only [spectralWeylIntegerSignMultiplier,ite_eq_right hmn] using
      spectralWeylKMultiplier_bounded_positive hX

theorem spectralWeylIntegerSignMultiplier_measurable (m n : ℤ) (X : ℝ) :
    Measurable (fun t : ℝ => spectralWeylIntegerSignMultiplier m n t X) := by
  by_cases hmn : 0 < m*n
  · simpa only [spectralWeylIntegerSignMultiplier,ite_eq_left hmn,Function.comp_def,id_eq] using
      spectralWeylJMultiplier_measurable.comp (measurable_id.prodMk measurable_const)
  · simpa only [spectralWeylIntegerSignMultiplier,ite_eq_right hmn,Function.comp_def,id_eq] using
      spectralWeylKMultiplier_measurable.comp (measurable_id.prodMk measurable_const)

theorem spectralABLRegularHeatKernel_integrable (m n : ℤ) {X : ℝ} (hX : 0 < X)
    (T ε : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    Integrable (fun t => spectralWeylIntegerSignMultiplier m n t X*
      spectralABLRegularCorrected T (T^(1-ε)) (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))
      spectralKLSpectralMeasure := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralABLRegularHeatProfile_properties T ε R hT hR).2.1
  obtain ⟨C,_,hb⟩ := spectralWeylIntegerSignMultiplier_bounded_positive m n hX
  have hi := spectralKLBoundedKernel_pair_integrable (fun t => spectralWeylIntegerSignMultiplier m n t X)
    (spectralWeylIntegerSignMultiplier_measurable m n X) C hb
    (spectralKLAnalysis (hG.toLp _)) (spectralKLAnalysis (hF.toLp _))
  apply hi.congr
  filter_upwards [spectralABLRegularHeatProfile_completed_analysis T ε R hT hR hG,
    spectralKLHeatProfile_completed_analysis R hR hF] with t htG htF
  rw [htG,htF,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylIntegerSignMultiplier m n t X*spectralABLRegularCorrected T (T^(1-ε)) (t : ℂ)*
        (spectralKLGaussianData R (t : ℂ)*spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralABLExceptionalHeatKernel_integrable (m n : ℤ) {X : ℝ} (hX : 0 < X)
    (a : ℝ) (A : ℕ) (hA : 1 ≤ A) (R : ℝ) (hR : 0 < R) :
    Integrable (fun t => spectralWeylIntegerSignMultiplier m n t X*
      spectralABLExceptionalCorrected a A (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))
      spectralKLSpectralMeasure := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralABLExceptionalHeatProfile_properties a A R hA hR).2.1
  obtain ⟨C,_,hb⟩ := spectralWeylIntegerSignMultiplier_bounded_positive m n hX
  have hi := spectralKLBoundedKernel_pair_integrable (fun t => spectralWeylIntegerSignMultiplier m n t X)
    (spectralWeylIntegerSignMultiplier_measurable m n X) C hb
    (spectralKLAnalysis (hG.toLp _)) (spectralKLAnalysis (hF.toLp _))
  apply hi.congr
  filter_upwards [spectralABLExceptionalHeatProfile_completed_analysis a A R hA hR hG,
    spectralKLHeatProfile_completed_analysis R hR hF] with t htG htF
  rw [htG,htF,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylIntegerSignMultiplier m n t X*spectralABLExceptionalCorrected a A (t : ℂ)*
        (spectralKLGaussianData R (t : ℂ)*spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralWeylRegularHeat_integer_sign {X : ℝ} (hX : 0 < X)
    (T ε : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    spectralWeylPhysicalBilinear
      (cuspFourierFrequency 1 m/|cuspFourierFrequency 1 m|)
      (cuspFourierFrequency 1 n/|cuspFourierFrequency 1 n|)
      (spectralABLRegularHeatProfile T ε R) (spectralKLHeatProfile R) X =
    spectralABLHeatKernel (spectralABLRegularCorrected T (T^(1-ε))) R m n X := by
  have hu := cuspFourierFrequency_ne_zero 1 zero_lt_one m hm
  have hv := cuspFourierFrequency_ne_zero 1 zero_lt_one n hn
  have hs := spectralWeyl_frequency_sign_sq hu
  have ht := spectralWeyl_frequency_sign_sq hv
  have he := spectralWeyl_frequency_sign_product hu hv
  have hpos := spectralWeyl_cusp_frequency_product_pos zero_lt_one m n
  by_cases hp : 0 < m*n
  · rw [ite_eq_left (hpos.mpr hp)] at he
    rw [spectralWeylRegularHeat_same_J hX T ε hT R hR _ _ hs ht he]
    simp only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_left hp]
  · rw [ite_eq_right (fun h => hp (hpos.mp h))] at he
    rw [spectralWeylRegularHeat_opposite_K hX T ε hT R hR _ _ hs ht he]
    simp only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_right hp]

theorem spectralWeylExceptionalHeat_integer_sign {X : ℝ} (hX : 0 < X)
    (a : ℝ) (A : ℕ) (hA : 1 ≤ A) (R : ℝ) (hR : 0 < R)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    spectralWeylPhysicalBilinear
      (cuspFourierFrequency 1 m/|cuspFourierFrequency 1 m|)
      (cuspFourierFrequency 1 n/|cuspFourierFrequency 1 n|)
      (spectralABLExceptionalHeatProfile a A R) (spectralKLHeatProfile R) X =
    spectralABLHeatKernel (spectralABLExceptionalCorrected a A) R m n X := by
  have hu := cuspFourierFrequency_ne_zero 1 zero_lt_one m hm
  have hv := cuspFourierFrequency_ne_zero 1 zero_lt_one n hn
  have hs := spectralWeyl_frequency_sign_sq hu
  have ht := spectralWeyl_frequency_sign_sq hv
  have he := spectralWeyl_frequency_sign_product hu hv
  have hpos := spectralWeyl_cusp_frequency_product_pos zero_lt_one m n
  by_cases hp : 0 < m*n
  · rw [ite_eq_left (hpos.mpr hp)] at he
    rw [spectralWeylExceptionalHeat_same_J hX a A hA R hR _ _ hs ht he]
    simp only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_left hp]
  · rw [ite_eq_right (fun h => hp (hpos.mp h))] at he
    rw [spectralWeylExceptionalHeat_opposite_K hX a A hA R hR _ _ hs ht he]
    simp only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_right hp]

def gamma0TrueWidthHeatFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (H : ℂ → ℂ) (R : ℝ) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N r s c.val m n*((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
    spectralABLHeatKernel H R m n (Real.sqrt (a*b)*(2/C))

theorem gamma0TrueWidthRegularHeatFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralABLRegularHeatProfile T ε R) (spectralKLHeatProfile R) =
    gamma0TrueWidthHeatFibre N r s c m n (spectralABLRegularCorrected T (T^(1-ε))) R := by
  have hm0 : 0 < |cuspFourierFrequency 1 m| := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hn0 : 0 < |cuspFourierFrequency 1 n| := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  unfold gamma0TrueWidthPhysicalFibre gamma0TrueWidthHeatFibre
  dsimp only
  rw [spectralWeylRegularHeat_integer_sign (by positivity) T ε hT R hR m n hm hn]

theorem gamma0TrueWidthExceptionalHeatFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralABLExceptionalHeatProfile a A R) (spectralKLHeatProfile R) =
    gamma0TrueWidthHeatFibre N r s c m n (spectralABLExceptionalCorrected a A) R := by
  have hm0 : 0 < |cuspFourierFrequency 1 m| := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hn0 : 0 < |cuspFourierFrequency 1 n| := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  unfold gamma0TrueWidthPhysicalFibre gamma0TrueWidthHeatFibre
  dsimp only
  rw [spectralWeylExceptionalHeat_integer_sign (by positivity) a A hA R hR m n hm hn]

theorem gamma0TrueWidthRegularHeatFibre_summable (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    Summable (fun c : Ioi (0 : ℕ) =>
      gamma0TrueWidthHeatFibre N r s c m n (spectralABLRegularCorrected T (T^(1-ε))) R) := by
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralABLRegularHeatProfile_properties T ε R hT hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralABLRegularHeatProfile_nonpositive_zero T ε R
  obtain ⟨M,hM,hbound⟩ := (spectralKLHeatRegularity_five_eighths _ hG hzG).2
  have hs := gamma0TrueWidthPhysicalFibre_moment_summable N r s m n hm hn
    (by norm_num : (1/2 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM _ _
    (spectralKLHeatRegularity_measurable _ hG hzG) (spectralKLHeatRegularity_measurable _ hF hzF)
    (spectralKLHeatRegularity_five_eighths _ hF hzF).1 hbound
  exact hs.congr (fun c => gamma0TrueWidthRegularHeatFibre N r s c m n hm hn T ε R hT hR)

theorem gamma0TrueWidthExceptionalHeatFibre_summable (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    Summable (fun c : Ioi (0 : ℕ) =>
      gamma0TrueWidthHeatFibre N r s c m n (spectralABLExceptionalCorrected a A) R) := by
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralABLExceptionalHeatProfile_properties a A R hA hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralABLExceptionalHeatProfile_nonpositive_zero a A R
  obtain ⟨M,hM,hbound⟩ := (spectralKLHeatRegularity_five_eighths _ hG hzG).2
  have hs := gamma0TrueWidthPhysicalFibre_moment_summable N r s m n hm hn
    (by norm_num : (1/2 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM _ _
    (spectralKLHeatRegularity_measurable _ hG hzG) (spectralKLHeatRegularity_measurable _ hF hzF)
    (spectralKLHeatRegularity_five_eighths _ hF hzF).1 hbound
  exact hs.congr (fun c => gamma0TrueWidthExceptionalHeatFibre N r s c m n hm hn a A R hA hR)

end ArtinMatthews
