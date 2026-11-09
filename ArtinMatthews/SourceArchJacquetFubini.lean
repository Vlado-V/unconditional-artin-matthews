module

public import ArtinMatthews.SourceArchJacquetLaplace


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute integrability and the actual Fourier-Laplace interchange for
the spherical Jacquet kernel. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory Set Filter
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

def sourceArchJacquetDenominator (r : ℝ) (z : ℂ) : ℝ :=
  (r ^ 2 + ‖z‖ ^ 2) ^ (-(4 / 3 : ℝ))

def sourceArchJacquetKernel (r : ℝ) (z : ℂ) : ℂ :=
  (r ^ (4 / 3 : ℝ) * sourceArchJacquetDenominator r z : ℝ) * sourceArchJacquetPhase z

def sourceArchJacquetIntegral (r : ℝ) : ℂ :=
  ∫ z : ℂ, sourceArchJacquetKernel r z ∂sourceComplexTraceMeasure

theorem sourceArchJacquetDenominator_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (sourceArchJacquetDenominator r) sourceComplexTraceMeasure := by
  have : SigmaFinite sourceComplexTraceMeasure := by
    change SigmaFinite ((2 : NNReal) • (volume : Measure ℂ))
    infer_instance
  have hi := (sourceArchJacquetLaplace_integrable hr).integral_prod_right
  change Integrable (fun z : ℂ => ∫ t in Ioi 0, sourceArchJacquetLaplace r t z)
    sourceComplexTraceMeasure at hi
  have he : (fun z : ℂ => ∫ t in Ioi 0, sourceArchJacquetLaplace r t z) =
      (fun z => Real.Gamma (4 / 3) * sourceArchJacquetDenominator r z) := by
    funext z
    exact sourceArchJacquetLaplace_point_integral hr z
  rw [he] at hi
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne') _).mp hi

theorem sourceArchJacquetKernel_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (sourceArchJacquetKernel r) sourceComplexTraceMeasure := by
  have hi := ((sourceArchJacquetDenominator_integrable hr).const_mul
    (r ^ (4 / 3 : ℝ))).ofReal (𝕜 := ℂ)
  apply hi.norm.mono'
    ((show Continuous (sourceArchJacquetKernel r) from by
      unfold sourceArchJacquetKernel sourceArchJacquetDenominator
      apply Continuous.mul
      · apply Complex.continuous_ofReal.comp
        apply continuous_const.mul
        exact (continuous_const.add (continuous_norm.pow 2)).rpow_const
          (fun z => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg _))))
      · exact sourceArchJacquetPhase_continuous).aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖((r ^ (4 / 3 : ℝ) * sourceArchJacquetDenominator r z : ℝ) : ℂ) *
      sourceArchJacquetPhase z‖ ≤ _
    rw [norm_mul, sourceArchJacquetPhase_norm, mul_one]
    exact le_rfl

theorem sourceArchJacquetLaplace_fourier (r : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, (sourceArchJacquetLaplace r t z : ℂ) * sourceArchJacquetPhase z
      ∂sourceComplexTraceMeasure) =
      ((2 * Real.pi) * (t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) : ℝ) := by
  unfold sourceArchJacquetLaplace
  simp_rw [Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul, integral_const_mul, sourceArchGaussianJacquet_integral ht]
  have hp : t ^ (1 / 3 : ℝ) / t = t ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = t ^ (1 / 3 : ℝ) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 / 3 : ℝ) - 1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by norm_num
  suffices t ^ (1 / 3 : ℝ) * (Real.exp (-(r ^ 2 * t)) *
      (2 * Real.pi / t * Real.exp (-(4 * Real.pi ^ 2) / t))) =
      (2 * Real.pi) * (t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) by
    have h := this
    rw [mul_assoc (2 : ℝ) Real.pi] at h
    exact_mod_cast h
  rw [Real.exp_sub]
  have hneg : Real.exp (-(4 * Real.pi ^ 2) / t) =
      (Real.exp ((4 * Real.pi ^ 2) / t))⁻¹ := by rw [neg_div, Real.exp_neg]
  rw [hneg]
  calc
    _ = (2 * Real.pi) * ((t ^ (1 / 3 : ℝ) / t) *
        (Real.exp (-(r ^ 2 * t)) / Real.exp ((4 * Real.pi ^ 2) / t))) := by ring
    _ = _ := by rw [hp]

theorem sourceArchJacquetIntegral_laplace {r : ℝ} (hr : 0 < r) :
    (Real.Gamma (4 / 3) : ℂ) * sourceArchJacquetIntegral r =
      (r ^ (4 / 3 : ℝ) * (2 * Real.pi) *
        ∫ t in Ioi 0, t ^ (-(2 / 3 : ℝ)) *
          Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t) : ℝ) := by
  have : SigmaFinite sourceComplexTraceMeasure := by
    change SigmaFinite ((2 : NNReal) • (volume : Measure ℂ))
    infer_instance
  have hswap := integral_integral_swap
    (f := fun t z => (sourceArchJacquetLaplace r t z : ℂ) * sourceArchJacquetPhase z)
    (sourceArchJacquetComplexLaplace_integrable hr)
  have hleft : (∫ t in Ioi 0, ∫ z : ℂ,
      (sourceArchJacquetLaplace r t z : ℂ) * sourceArchJacquetPhase z
        ∂sourceComplexTraceMeasure) =
      ((2 * Real.pi) * ∫ t in Ioi 0, t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t) : ℝ) := by
    calc
      _ = ∫ t in Ioi 0, (((2 * Real.pi) * (t ^ (-(2 / 3 : ℝ)) *
          Real.exp (-(r ^ 2 * t) - (4 * Real.pi ^ 2) / t)) : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact sourceArchJacquetLaplace_fourier r ht
      _ = _ := by rw [integral_complex_ofReal, integral_const_mul]
  have hright : (∫ z : ℂ, (∫ t in Ioi 0,
      (sourceArchJacquetLaplace r t z : ℂ) * sourceArchJacquetPhase z)
        ∂sourceComplexTraceMeasure) =
      (Real.Gamma (4 / 3) : ℂ) * ∫ z : ℂ,
        (sourceArchJacquetDenominator r z : ℂ) * sourceArchJacquetPhase z
          ∂sourceComplexTraceMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only
      rw [integral_mul_const, integral_complex_ofReal, sourceArchJacquetLaplace_point_integral hr,
        Complex.ofReal_mul, mul_assoc]
      rfl
  rw [hleft, hright] at hswap
  unfold sourceArchJacquetIntegral sourceArchJacquetKernel
  simp_rw [Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul]
  calc
    _ = ((r ^ (4 / 3 : ℝ) : ℝ) : ℂ) *
      ((Real.Gamma (4 / 3) : ℂ) * ∫ z : ℂ,
        (sourceArchJacquetDenominator r z : ℂ) * sourceArchJacquetPhase z
          ∂sourceComplexTraceMeasure) := by ring
    _ = _ := by rw [← hswap]; push_cast; ring

end
end ArtinMatthews.SourceArchJacquet
