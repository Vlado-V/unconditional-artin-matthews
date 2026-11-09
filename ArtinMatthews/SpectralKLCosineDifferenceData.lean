module

public import ArtinMatthews.SpectralKLCoshInversion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine spectral datum for a cosh-exponential difference. Its
weighted L2 convergence follows from elementary cosine and sinh bounds. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralKLCosineDifferenceData (u v t : ℝ) : ℂ :=
  ((Real.pi*(Real.cos (t*u)-Real.cos (t*v))/(t*Real.sinh (Real.pi*t)) : ℝ) : ℂ)

theorem spectralKLCosineDifferenceData_measurable (u v : ℝ) :
    Measurable (spectralKLCosineDifferenceData u v) := by
  unfold spectralKLCosineDifferenceData
  fun_prop

theorem spectralKLCosineDifferenceData_contDiffOn (u v : ℝ) :
    ContDiffOn ℝ ∞ (spectralKLCosineDifferenceData u v) (Ioi (0 : ℝ)) := by
  have hc : ContDiffOn ℝ ∞ (fun t : ℝ =>
      Real.pi*(Real.cos (t*u)-Real.cos (t*v))/(t*Real.sinh (Real.pi*t))) (Ioi (0 : ℝ)) := by
    apply ContDiffOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero ht.ne' (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hc

theorem spectralKLCosineDifferenceData_weighted_square (u v t : ℝ) (ht : 0 < t) :
    spectralKLPlancherelWeight t*‖spectralKLCosineDifferenceData u v t‖^2 =
      2*(Real.cos (t*u)-Real.cos (t*v))^2/(t*Real.sinh (Real.pi*t)) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hs0 : Real.sinh (Real.pi*t) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  unfold spectralKLPlancherelWeight spectralKLCosineDifferenceData
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  field_simp

theorem spectralKLCosineDifferenceData_weight_mul (u v t : ℝ) (ht : 0 < t) :
    (spectralKLPlancherelWeight t : ℂ)*spectralKLCosineDifferenceData u v t =
      ((2/Real.pi*(Real.cos (t*u)-Real.cos (t*v)) : ℝ) : ℂ) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hs0 : Real.sinh (Real.pi*t) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have hsc : (Real.sinh (Real.pi*t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0
  have hpc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold spectralKLPlancherelWeight spectralKLCosineDifferenceData
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
  field_simp

theorem spectral_cosine_difference_square_bounds (u v t : ℝ) (ht : 0 < t) :
    (Real.cos (t*u)-Real.cos (t*v))^2 ≤ (u-v)^2*t^2 ∧
      (Real.cos (t*u)-Real.cos (t*v))^2 ≤ 4 := by
  have hLip : |Real.cos (t*u)-Real.cos (t*v)| ≤ |u-v| * t := by
    have h := Real.abs_cos_sub_cos_le (t*u) (t*v)
    rw [show t*u-t*v = (u-v)*t by ring,abs_mul,abs_of_pos ht] at h
    exact h
  have hUniform : |Real.cos (t*u)-Real.cos (t*v)| ≤ 2 := by
    calc
      _ ≤ |Real.cos (t*u)|+|Real.cos (t*v)| := abs_sub _ _
      _ ≤ 1+1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = _ := by norm_num
  have hsq : (Real.cos (t*u)-Real.cos (t*v))^2 ≤ (u-v)^2*t^2 := by
    calc
      _ = |Real.cos (t*u)-Real.cos (t*v)|^2 := (sq_abs _).symm
      _ ≤ (|u-v| * t)^2 := by gcongr
      _ = _ := by rw [mul_pow,sq_abs]
  exact ⟨hsq,by nlinarith [sq_abs (Real.cos (t*u)-Real.cos (t*v)),abs_nonneg (Real.cos (t*u)-Real.cos (t*v))]⟩

theorem spectralKLCosineDifferenceData_cauchy_bound (u v t : ℝ) (ht : 0 < t) :
    spectralKLPlancherelWeight t*‖spectralKLCosineDifferenceData u v t‖^2 ≤
      ((2/Real.pi)*((u-v)^2+4))/(1+t^2) := by
  let E : ℝ := spectralKLPlancherelWeight t*‖spectralKLCosineDifferenceData u v t‖^2
  have hE := spectralKLCosineDifferenceData_weighted_square u v t ht
  have hden : 0 < t*Real.sinh (Real.pi*t) := mul_pos ht (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))
  have hden0 : 0 < Real.pi*t^2 := mul_pos Real.pi_pos (sq_pos_of_pos ht)
  have hsinh : Real.pi*t ≤ Real.sinh (Real.pi*t) := Real.self_le_sinh_iff.mpr (mul_nonneg Real.pi_pos.le ht.le)
  have hdenle : Real.pi*t^2 ≤ t*Real.sinh (Real.pi*t) := by nlinarith
  have hEle : E ≤ 2*(Real.cos (t*u)-Real.cos (t*v))^2/(Real.pi*t^2) := by
    dsimp [E]
    rw [hE]
    exact div_le_div_of_nonneg_left (mul_nonneg two_pos.le (sq_nonneg _)) hden0 hdenle
  obtain ⟨hLip,hUniform⟩ := spectral_cosine_difference_square_bounds u v t ht
  have hA : E ≤ (2/Real.pi)*(u-v)^2 := by
    calc
      _ ≤ 2*(Real.cos (t*u)-Real.cos (t*v))^2/(Real.pi*t^2) := hEle
      _ ≤ 2*((u-v)^2*t^2)/(Real.pi*t^2) := by gcongr
      _ = _ := by field_simp
  have hB : t^2*E ≤ 8/Real.pi := by
    calc
      _ ≤ t^2*(2*(Real.cos (t*u)-Real.cos (t*v))^2/(Real.pi*t^2)) :=
        mul_le_mul_of_nonneg_left hEle (sq_nonneg _)
      _ = 2*(Real.cos (t*u)-Real.cos (t*v))^2/Real.pi := by field_simp
      _ ≤ 8/Real.pi := by gcongr; nlinarith
  change E ≤ _
  apply (le_div_iff₀ (show 0 < 1+t^2 by positivity)).mpr
  calc
    E*(1+t^2) = E+t^2*E := by ring
    _ ≤ (2/Real.pi)*(u-v)^2+8/Real.pi := add_le_add hA hB
    _ = _ := by ring

theorem spectralKLCosineDifferenceData_memLp (u v : ℝ) :
    MemLp (spectralKLCosineDifferenceData u v) 2 spectralKLSpectralMeasure := by
  have hm := (spectralKLCosineDifferenceData_measurable u v).aestronglyMeasurable (μ := spectralKLSpectralMeasure)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  change Integrable _ (spectralKLPositiveWeightMeasure spectralKLPlancherelWeight)
  apply (spectralKLPositiveWeightMeasure_integrable_iff spectralKLPlancherelWeight
    (fun t => ‖spectralKLCosineDifferenceData u v t‖^2) spectralKLPlancherelWeight_continuous.measurable
      (fun t ht => (spectralKLPlancherelWeight_pos ht).le)).mpr
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => spectralKLPlancherelWeight t*‖spectralKLCosineDifferenceData u v t‖^2)
      (volume.restrict (Ioi 0)) := by
    unfold spectralKLCosineDifferenceData spectralKLPlancherelWeight
    fun_prop
  apply ((integrable_inv_one_add_sq.const_mul ((2/Real.pi)*((u-v)^2+4))).restrict).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (spectralKLPlancherelWeight_pos ht).le (sq_nonneg _))]
  simpa only [div_eq_mul_inv] using spectralKLCosineDifferenceData_cauchy_bound u v t ht

end ArtinMatthews
