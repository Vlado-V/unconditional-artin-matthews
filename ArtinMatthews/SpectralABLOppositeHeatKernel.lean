module

public import ArtinMatthews.SpectralWeylHeatRapidWeight
public import ArtinMatthews.SpectralBareModulusSeries


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter Complex
open scoped ContDiff Topology MatrixGroups
noncomputable section

theorem spectralABLOppositeFourierWeight_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => spectralABLOppositeFourierWeight f (t : ℂ)) spectralKLSpectralMeasure := by
  let H := spectralABLOppositeFourierWeight f
  have hH := (spectralABLOppositeFourierWeight_real_smooth f hf.continuous hc hp).continuous
  obtain ⟨D,hD,hbound⟩ := spectralABLOppositeFourierWeight_normalized_rapid f hf hc hp 2
  have hpw (t : ℝ) (ht : 0 < t) : 0 ≤ spectralKLPlancherelWeight t :=
    (spectralKLPlancherelWeight_pos ht).le
  apply (spectralKLPositiveWeightMeasure_complex_integrable_iff _ _
    spectralKLPlancherelWeight_continuous.measurable hpw).mpr
  have hmajor : Integrable (fun t : ℝ => ((2/Real.pi^2)*D)*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hmajor.restrict.mono'
    ((Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).mul hH).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  let u : ℝ := 1+t^2
  let E := Real.exp (Real.pi*|t|)
  have hu : 0 < u := by dsimp [u]; positivity
  have hht : E*‖H (t : ℂ)‖ ≤ D/u^2 := (le_div_iff₀ (pow_pos hu _)).mpr (by
    simpa only [H,u,E,Complex.ofReal_zero,zero_mul,mul_zero,add_zero,mul_assoc,mul_left_comm,mul_comm]
      using hbound t 0 (by norm_num))
  have hw := spectralKLPlancherelWeight_abs_bound t
  have htu : |t| ≤ u := by dsimp [u]; nlinarith [sq_abs t,sq_nonneg (|t|-1/2)]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  change |spectralKLPlancherelWeight t| * ‖H (t : ℂ)‖ ≤ ((2/Real.pi^2)*D)*u⁻¹
  calc
    _ ≤ ((2/Real.pi^2)*|t| *E)*‖H (t : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = ((2/Real.pi^2)*|t|)*(E*‖H (t : ℂ)‖) := by ring
    _ ≤ ((2/Real.pi^2)*u)*(D/u^2) := by gcongr
    _ = _ := by field_simp [hu.ne'] <;> ring

theorem spectralABLOppositeHeatKernel_small_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (m n : ℤ) (X₀ : ℝ) (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
      ‖spectralABLHeatKernel (spectralABLOppositeFourierWeight f) R m n X‖ ≤
        C*X^(1/4 : ℝ) := by
  obtain ⟨D,hD,hb⟩ := spectralABLOppositeFourierWeight_normalized_rapid f hf hc hp 3
  exact spectralWeylHeat_small_of_exp_rapid _ (spectralABLOppositeFourierWeight_even f hp)
    (fun z _ _ => spectralABLOppositeFourierWeight_entire f hf.continuous hc hp z)
    D hD (fun t y hy0 hy1 => hb t y (by rw [abs_of_nonneg hy0]; linarith))
    m n X₀ hX₀

theorem spectralABLOppositeBareKernel_inverse (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    {m n : ℤ} (hmn : m*n < 0) {X : ℝ} (hX : 0 < X) :
    ((X : ℂ)/2)*spectralABLBareKernel (spectralABLOppositeFourierWeight f) m n X =
      f X/(Real.pi : ℂ) := by
  simpa only [spectralABLBareKernel,spectralWeylIntegerSignMultiplier,
    ite_eq_right (not_lt_of_ge hmn.le)] using
    (spectralABLOppositeTransform_bare_inverse f hf hc hp hX).2

theorem spectralABLOppositeHeatKernel_tendsto (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    {m n : ℤ} (hmn : m*n < 0) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => ((X : ℂ)/2)*
      spectralABLHeatKernel (spectralABLOppositeFourierWeight f) R m n X) atTop
      (𝓝 (f X/(Real.pi : ℂ))) := by
  rw [← spectralABLOppositeBareKernel_inverse f hf hc hp hmn hX]
  exact (spectralABLHeatKernel_tendsto_bare _ (spectralABLOppositeFourierWeight_integrable f hf hc hp)
    m n hX).const_mul _

end
end ArtinMatthews
