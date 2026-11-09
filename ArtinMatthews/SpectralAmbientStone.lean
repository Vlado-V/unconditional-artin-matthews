module

public import ArtinMatthews.SpectralAmbientStieltjes
public import ArtinMatthews.SpectralPoissonMeasureLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full ambient resolvent gives Stone inversion for its
genuine scalar spectral measure, with the exact 1/π normalization. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology CompactlySupported
namespace ArtinMatthews

def spectralEnergyShift (x ε : ℝ) : ℂ := (x:ℂ)+(ε:ℂ)*Complex.I

theorem spectralEnergyShift_re (x ε : ℝ) : (spectralEnergyShift x ε).re=x := by
  simp [spectralEnergyShift,Complex.mul_re]

theorem spectralEnergyShift_im (x ε : ℝ) : (spectralEnergyShift x ε).im=ε := by
  simp [spectralEnergyShift,Complex.mul_im]

theorem spectralEnergyShift_offcut (x ε : ℝ) (hε : ε≠0) :
    (spectralEnergyShift x ε).re<‖spectralEnergyShift x ε‖ :=
  (le_abs_self _).trans_lt (Complex.abs_re_lt_norm.mpr (by simpa only [spectralEnergyShift_im] using hε))

theorem spectralStieltjesKernel_im_poisson (x ε l : ℝ) :
    (((l:ℂ)-spectralEnergyShift x ε)⁻¹).im=spectralPoissonPeak ε (x-l) := by
  let z := (l:ℂ)-spectralEnergyShift x ε
  have h := RCLike.inv_im z
  rw [RCLike.normSq_apply] at h
  change (z⁻¹).im= -z.im/(z.re*z.re+z.im*z.im) at h
  change (z⁻¹).im=_
  rw [h]
  dsimp only [z]
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    spectralEnergyShift_re,spectralEnergyShift_im,zero_sub,neg_neg,neg_mul_neg,spectralPoissonPeak]
  congr 1
  ring

theorem gamma0AmbientResolventFamily_im_poisson (N : ℕ) [NeZero N]
    (x ε : ℝ) (hε : ε≠0) (u : Gamma0RegionL2 N) :
    (inner ℂ u (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) u)).im=
      spectralPoissonMeasureTransform (gamma0AmbientSpectralMeasure N u) ε x := by
  let μ := gamma0AmbientSpectralMeasure N u
  let z := spectralEnergyShift x ε
  have hz : z.re<‖z‖ := spectralEnergyShift_offcut x ε hε
  have hi := gamma0AmbientSpectralMeasure_kernel_integrable N z hz u
  have hI : (∫ l,(((l:ℂ)-z)⁻¹).im ∂μ)=(∫ l,((l:ℂ)-z)⁻¹ ∂μ).im :=
    Complex.imCLM.integral_comp_comm hi
  rw [gamma0AmbientResolventFamily_stieltjes N z hz,← hI]
  exact integral_congr_ae (Eventually.of_forall (spectralStieltjesKernel_im_poisson x ε))

theorem gamma0AmbientResolventFamily_diagonal_conj (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (u : Gamma0RegionL2 N) :
    (starRingEnd ℂ) (inner ℂ u (gamma0AmbientResolventFamily N z u))=
      inner ℂ u (gamma0AmbientResolventFamily N ((starRingEnd ℂ) z) u) := by
  let μ := gamma0AmbientSpectralMeasure N u
  have hc : ((starRingEnd ℂ) z).re<‖(starRingEnd ℂ) z‖ := by
    simpa only [Complex.conj_re,Complex.norm_conj] using hz
  rw [gamma0AmbientResolventFamily_stieltjes N z hz,gamma0AmbientResolventFamily_stieltjes N _ hc]
  have hI : (∫ l : ℝ,(starRingEnd ℂ) (((l:ℂ)-z)⁻¹) ∂μ)=
      (starRingEnd ℂ) (∫ l : ℝ,((l:ℂ)-z)⁻¹ ∂μ) :=
    Complex.conjLIE.toLinearIsometry.integral_comp_comm (fun l : ℝ => ((l:ℂ)-z)⁻¹)
  rw [← hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun l => by
    change (starRingEnd ℂ) (((l:ℂ)-z)⁻¹)=((l:ℂ)-(starRingEnd ℂ) z)⁻¹
    rw [map_inv₀,map_sub,Complex.conj_ofReal]

theorem gamma0AmbientSpectralMeasure_stone (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N)
    (f : C_c(ℝ,ℝ)) :
    Tendsto (fun ε : ℝ => Real.pi⁻¹*(∫ x : ℝ,
      (inner ℂ u (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) u)).im*f x))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ l,f l ∂gamma0AmbientSpectralMeasure N u)) := by
  apply (spectralPoissonCompactTest_limit (gamma0AmbientSpectralMeasure N u) f).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  simp_rw [gamma0AmbientResolventFamily_im_poisson N _ ε hε.ne' u]

end ArtinMatthews
