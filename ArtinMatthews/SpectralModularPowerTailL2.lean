module

public import ArtinMatthews.SpectralCuspProjectedConstant
public import ArtinMatthews.SpectralCuspComplexEulerEnergy
public import ArtinMatthews.SpectralEisensteinVerticalCutoff
public import ArtinMatthews.SpectralModularTailIntegral
public import ArtinMatthews.SpectralModularTailBoundedL2


set_option backward.privateInPublic true
@[expose] public section

/-! Actual modular-region L2 from the true polynomial cusp tail threshold.
The hyperbolic measure gives the precise condition Re(q)<1/2. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralHeightPower_norm_sq_continuous (q : ℂ) :
    Continuous (fun z : UpperHalfPlane => ‖(z.im:ℂ)^q‖^2) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (((eisensteinPositivePower_hasDerivAt q z.im z.im_pos).continuousAt.comp
    UpperHalfPlane.continuous_im.continuousAt).norm.pow 2)

theorem spectralCuspHeightPower_norm_sq_integrable (w Y : ℝ) (hw : 0<w) (hY : 0<Y)
    (q : ℂ) (hq : q.re<1/2) :
    IntegrableOn (fun z : UpperHalfPlane => ‖(z.im:ℂ)^q‖^2) (hyperbolicCuspStrip w Y) volume := by
  have hv := (cuspVerticalL2_integrable_density_iff hw hY (fun y => ‖(y:ℂ)^q‖^2)).mpr
    (by simpa only [one_mul] using cuspComplexEuler_power_energy_integrable (1:ℂ) hY hq)
  exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hv).comp_measurePreserving
    (cusp_height_measurePreserving w Y hY))

theorem spectralModularHeightPower_norm_sq_integrable_tail (Y : ℝ) (hY : 0<Y)
    (q : ℂ) (hq : q.re<1/2) :
    IntegrableOn (fun z : UpperHalfPlane => ‖(z.im:ℂ)^q‖^2)
      {z | z∈ModularGroup.fd ∧ Y<z.im} volume := by
  let g : UpperHalfPlane → ℝ := fun z => ‖(z.im:ℂ)^q‖^2
  have he : (fun z : UpperHalfPlane => g (ModularGroup.T⁻¹ • z))=g := by
    funext z
    change ‖(((ModularGroup.T⁻¹ • z).im:ℝ):ℂ)^q‖^2=‖(z.im:ℂ)^q‖^2
    rw [← zpow_neg_one,ModularGroup.im_T_zpow_smul]
  have h : IntegrableOn g (hyperbolicCuspStrip ((1:ℕ):ℝ) Y) volume := by
    simpa only [Nat.cast_one,g] using spectralCuspHeightPower_norm_sq_integrable 1 Y zero_lt_one hY q hq
  have h' : IntegrableOn (fun z : UpperHalfPlane => g (ModularGroup.T⁻¹ • z))
      (hyperbolicCuspStrip ((1:ℕ):ℝ) Y) volume := by rw [he];exact h
  exact (modular_tail_integrable_integral_le_two_strips 1 Y g (fun _ => sq_nonneg _)
    (spectralHeightPower_norm_sq_continuous q).aestronglyMeasurable h h').1

theorem continuous_memLp_modular_of_power_tail {E : Type*} [NormedAddCommGroup E]
    (F : UpperHalfPlane → E) (hF : Continuous F) (r : SL(2,ℤ))
    (Y C : ℝ) (hY : 0<Y) (hC : 0≤C) (q : ℂ) (hq : q.re<1/2)
    (htail : ∀ z : UpperHalfPlane, z∈ModularGroup.fd → Y<z.im →
      ‖F (r⁻¹ • z)‖ ≤ C*‖(z.im:ℂ)^q‖) :
    MemLp (fun z : UpperHalfPlane => F (r⁻¹ • z)) 2 (volume.restrict ModularGroup.fd) := by
  let L : Set UpperHalfPlane := {z | z∈ModularGroup.fd ∧ z.im≤Y}
  let T : Set UpperHalfPlane := {z | z∈ModularGroup.fd ∧ Y<z.im}
  let K : Set UpperHalfPlane := {z | (z.re,z.im)∈spectralPlaneRectangle (1/2) (1/2) Y}
  have hK : IsCompact K := spectralCoreChart_compact (1/2) (1/2) Y (by norm_num)
  have hLc : IsClosed L := ModularGroup.isClosed_fd.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)
  have hLK : L⊆K := by
    intro z hz
    change (-(1/2:ℝ)≤z.re ∧ z.re≤1/2) ∧ 1/2≤z.im ∧ z.im≤Y
    refine ⟨abs_le.mp hz.1.2,?_,hz.2⟩
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz.1,z.im_pos]
  have hTc : MeasurableSet T := ModularGroup.isClosed_fd.measurableSet.inter
    (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hF' : Continuous (fun z : UpperHalfPlane => F (r⁻¹ • z)) := by
    change Continuous (fun z : UpperHalfPlane => F (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z))
    exact hF.comp (continuous_const_smul _)
  have hL : IntegrableOn (fun z : UpperHalfPlane => ‖F (r⁻¹ • z)‖^2) L volume :=
    (hF'.norm.pow 2).continuousOn.integrableOn_compact (hK.of_isClosed_subset hLc hLK)
  have hT : IntegrableOn (fun z : UpperHalfPlane => ‖F (r⁻¹ • z)‖^2) T volume := by
    apply ((spectralModularHeightPower_norm_sq_integrable_tail Y hY q hq).const_mul (C^2)).mono'
      (hF'.norm.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hTc] with z hz
    change ‖‖F (r⁻¹ • z)‖^2‖≤C^2*‖(z.im:ℂ)^q‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _),← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (htail z hz.1 hz.2)
  have he : ModularGroup.fd=L∪T := by
    ext z
    change z∈ModularGroup.fd ↔ (z∈ModularGroup.fd ∧ z.im≤Y) ∨ (z∈ModularGroup.fd ∧ Y<z.im)
    exact ⟨fun hz => (le_or_gt z.im Y).imp (fun h => ⟨hz,h⟩) (fun h => ⟨hz,h⟩),
      fun hz => hz.elim And.left And.left⟩
  apply (memLp_two_iff_integrable_sq_norm hF'.aestronglyMeasurable).mpr
  change IntegrableOn _ ModularGroup.fd volume
  rw [he]
  exact hL.union hT

end ArtinMatthews
