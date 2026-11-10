module

public import ArtinMatthews.SpectralKLGaussianData
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralHorizontalContour
public import ArtinMatthews.SpectralWeylGaussianLimit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter Complex
open scoped Topology
noncomputable section

theorem spectralKLGaussianData_strip_norm_le {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    (t y : ℝ) (hy : |y| ≤ B) :
    ‖spectralKLGaussianData R ((t : ℂ)+(y : ℂ)*I)‖ ≤ Real.exp (B^2) := by
  have hy2 : y^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hB).mpr hy
  have hR2 : (1 : ℝ) ≤ R^2 := one_le_pow₀ hR
  rw [spectralKLGaussianData_norm_shift]
  apply Real.exp_le_exp.mpr
  have hd : (y/R)^2 ≤ B^2 := by
    rw [div_pow]
    exact (div_le_div_of_nonneg_right hy2 (sq_nonneg R)).trans (div_le_self (sq_nonneg B) hR2)
  linarith [sq_nonneg (t/R)]

theorem spectral_horizontal_gaussian_tendsto (F : ℂ → ℂ) (y : ℝ)
    (hF : Integrable (fun t : ℝ => F ((t : ℂ)+(y : ℂ)*I))) :
    Tendsto (fun R : ℝ => ∫ t : ℝ, F ((t : ℂ)+(y : ℂ)*I)*
      Complex.exp (-2*(((t : ℂ)+(y : ℂ)*I)/(R : ℂ))^2)) atTop
      (𝓝 (∫ t : ℝ, F ((t : ℂ)+(y : ℂ)*I))) := by
  let E := Real.exp (|y|^2)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => E*‖F ((t : ℂ)+(y : ℂ)*I)‖)
  · exact Eventually.of_forall fun R => hF.aestronglyMeasurable.mul
      ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-2*(((t : ℂ)+(y : ℂ)*I)/(R : ℂ))^2))).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact ae_of_all _ fun t => by
      rw [norm_mul,spectralWeylGaussian_eq_square,norm_pow,mul_comm E]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _)
        (spectralKLGaussianData_strip_norm_le hR (abs_nonneg y) t y le_rfl) 2
  · exact hF.norm.const_mul E
  · exact ae_of_all _ fun t => by
      simpa only [mul_one] using
        (spectralWeylGaussian_tendsto_one ((t : ℂ)+(y : ℂ)*I)).const_mul (F ((t : ℂ)+(y : ℂ)*I))

theorem spectral_horizontal_integral_eq_of_gaussian_envelope (F : ℂ → ℂ) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ B → DifferentiableAt ℂ F z)
    (hbound : ∀ t y : ℝ, 0 ≤ y → y ≤ B →
      ‖F ((t : ℂ)+(y : ℂ)*I)‖ ≤ C*(1+t^2)*Real.exp (Real.pi*|t|))
    (h0 : Integrable (fun t : ℝ => F (t : ℂ)))
    (hTop : Integrable (fun t : ℝ => F ((t : ℂ)+(B : ℂ)*I))) :
    (∫ t : ℝ, F (t : ℂ)) = ∫ t : ℝ, F ((t : ℂ)+(B : ℂ)*I) := by
  have hshift (R : ℝ) (hR : 1 ≤ R) :
      (∫ t : ℝ, F (t : ℂ)*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)) =
        ∫ t : ℝ, F ((t : ℂ)+(B : ℂ)*I)*Complex.exp (-2*(((t : ℂ)+(B : ℂ)*I)/(R : ℂ))^2) := by
    let E := Real.exp (B^2)
    obtain ⟨D,hD,hRapid⟩ := spectralKLGaussianData_strip_rapid R (by linarith) Real.pi B hB 2
    apply spectral_horizontal_integral_eq_of_heightWeight
      (fun z => F z*Complex.exp (-2*(z/(R : ℂ))^2)) (C:=C*E*D) hB
    · intro z hz0 hzB
      exact (hhol z hz0 hzB).mul (by fun_prop)
    · intro t y hy0 hyB
      let z : ℂ := (t : ℂ)+(y : ℂ)*I
      let u := 1+t^2
      have hu : 0 < u := by dsimp [u]; positivity
      have hy : |y| ≤ B := by simpa only [abs_of_nonneg hy0] using hyB
      have hG : ‖spectralKLGaussianData R z‖ ≤ E := spectralKLGaussianData_strip_norm_le hR hB t y hy
      have hG2 : ‖spectralKLGaussianData R z‖^2 ≤ ‖spectralKLGaussianData R z‖*E := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hG (norm_nonneg _)
      change ‖F z*Complex.exp (-2*(z/(R : ℂ))^2)‖ ≤ _
      rw [norm_mul,spectralWeylGaussian_eq_square,norm_pow]
      calc
        _ ≤ (C*u*Real.exp (Real.pi*|t|))*(‖spectralKLGaussianData R z‖*E) :=
          mul_le_mul (hbound t y hy0 hyB) hG2 (by positivity) (by positivity)
        _ = (C*E/u)*(u^2*Real.exp (Real.pi*|t|)*‖spectralKLGaussianData R z‖) := by
          field_simp [hu.ne']
        _ ≤ (C*E/u)*D := mul_le_mul_of_nonneg_left (hRapid t y hy) (by positivity)
        _ = _ := by simp only [SourcePhysical.sourceContourHeightWeight,u,div_eq_mul_inv]; ring
  have hlim0 := spectral_horizontal_gaussian_tendsto F 0 (by
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using h0)
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hlim0
  have hlimB := spectral_horizontal_gaussian_tendsto F B hTop
  apply tendsto_nhds_unique hlim0
  apply hlimB.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact (hshift R hR).symm

end
end ArtinMatthews
