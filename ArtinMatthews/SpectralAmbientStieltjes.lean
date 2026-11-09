module

public import ArtinMatthews.SpectralAmbientGreenCalculus


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine scalar spectral measure in energy coordinates and the
actual Stieltjes transform of the full ambient resolvent. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0GreenQuadraticMeasure (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    Measure (spectrum ℂ (gamma0Green N)) :=
  spectralQuadraticMeasure (gamma0Green N) (gamma0Green_selfAdjoint N).isStarNormal u

def gamma0GreenPositiveSpectrum (N : ℕ) [NeZero N] : Set (spectrum ℂ (gamma0Green N)) :=
  {x | 0<(x:ℂ).re}

def gamma0GreenEnergyCoordinate (N : ℕ) [NeZero N] (x : spectrum ℂ (gamma0Green N)) : ℝ :=
  (x:ℂ).re⁻¹-1

theorem gamma0GreenPositiveSpectrum_measurable (N : ℕ) [NeZero N] :
    MeasurableSet (gamma0GreenPositiveSpectrum N) :=
  measurableSet_lt measurable_const (Complex.continuous_re.measurable.comp measurable_subtype_coe)

theorem gamma0GreenEnergyCoordinate_measurable (N : ℕ) [NeZero N] :
    Measurable (gamma0GreenEnergyCoordinate N) :=
  ((Complex.continuous_re.measurable.comp measurable_subtype_coe).inv).sub measurable_const

def gamma0AmbientSpectralMeasure (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) : Measure ℝ :=
  Measure.map (gamma0GreenEnergyCoordinate N)
    ((gamma0GreenQuadraticMeasure N u).restrict (gamma0GreenPositiveSpectrum N))

instance gamma0AmbientSpectralMeasure_isFinite (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    IsFiniteMeasure (gamma0AmbientSpectralMeasure N u) := by
  unfold gamma0AmbientSpectralMeasure gamma0GreenQuadraticMeasure
  exact Measure.isFiniteMeasure_map _ _

theorem gamma0GreenEnergyCoordinate_nonneg (N : ℕ) [NeZero N] {x : spectrum ℂ (gamma0Green N)}
    (hx : x∈gamma0GreenPositiveSpectrum N) : 0≤gamma0GreenEnergyCoordinate N x := by
  obtain ⟨r,_,hr1,he⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  have hR : (x:ℂ).re=r := by simpa only [Complex.ofReal_re] using congrArg Complex.re he
  change 0<(x:ℂ).re at hx
  rw [hR] at hx
  rw [gamma0GreenEnergyCoordinate,hR,sub_nonneg,← one_div]
  exact (le_div_iff₀ hx).mpr (by simpa only [one_mul] using hr1)

theorem gamma0AmbientSpectralMeasure_ae_nonneg (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    ∀ᵐ l ∂gamma0AmbientSpectralMeasure N u,0≤l := by
  unfold gamma0AmbientSpectralMeasure
  apply (ae_map_iff (gamma0GreenEnergyCoordinate_measurable N).aemeasurable
    (measurableSet_Ici : MeasurableSet (Ici (0:ℝ)))).mpr
  filter_upwards [ae_restrict_mem (gamma0GreenPositiveSpectrum_measurable N)] with x hx
  exact gamma0GreenEnergyCoordinate_nonneg N hx

theorem gamma0GreenResolventSymbol_eq_energy (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (x : spectrum ℂ (gamma0Green N))
    (hx : x∈gamma0GreenPositiveSpectrum N) :
    gamma0GreenResolventSymbol N z hz x=((gamma0GreenEnergyCoordinate N x:ℂ)-z)⁻¹ := by
  obtain ⟨r,_,_,hr⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  have hR : ((x:ℂ).re:ℂ)=(x:ℂ) := by rw [hr,Complex.ofReal_re]
  have hX : (x:ℂ)≠0 := by
    have h : 0<(x:ℂ).re := hx
    intro he
    rw [he,Complex.zero_re] at h
    exact (lt_irrefl _ h)
  have hD := gamma0Green_spectrum_resolvent_denominator_ne_zero N z hz x
  change (x:ℂ)/(1-(z+1)*(x:ℂ))=((((x:ℂ).re⁻¹-1:ℝ):ℂ)-z)⁻¹
  rw [Complex.ofReal_sub,Complex.ofReal_inv,Complex.ofReal_one,hR]
  have hFactor : (((x:ℂ)⁻¹-1-z)*(x:ℂ))=1-(z+1)*(x:ℂ) := by
    rw [sub_mul,sub_mul,inv_mul_cancel₀ hX]
    ring
  rw [← hFactor]
  have hn : (x:ℂ)⁻¹-1-z≠0 := fun he => hD (hFactor.symm.trans (by rw [he,zero_mul]))
  field_simp [hX,hn]

theorem gamma0GreenResolventSymbol_zero_outside (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (x : spectrum ℂ (gamma0Green N))
    (hx : x∉gamma0GreenPositiveSpectrum N) :
    gamma0GreenResolventSymbol N z hz x=0 := by
  obtain ⟨r,hr,_,he⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  change ¬0<(x:ℂ).re at hx
  rw [he,Complex.ofReal_re] at hx
  have hz0 : r=0 := le_antisymm (le_of_not_gt hx) hr
  change (x:ℂ)/(1-(z+1)*(x:ℂ))=0
  rw [he,hz0,Complex.ofReal_zero,zero_div]

theorem spectralStieltjesKernel_measurable (z : ℂ) :
    Measurable (fun l : ℝ => ((l:ℂ)-z)⁻¹) :=
  (Complex.continuous_ofReal.measurable.sub measurable_const).inv

theorem gamma0AmbientSpectralMeasure_kernel_integrable (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (u : Gamma0RegionL2 N) :
    Integrable (fun l : ℝ => ((l:ℂ)-z)⁻¹) (gamma0AmbientSpectralMeasure N u) := by
  let μ := gamma0GreenQuadraticMeasure N u
  let U := gamma0GreenPositiveSpectrum N
  let f := gamma0GreenResolventSymbol N z hz
  have hf : Integrable f μ := by
    unfold μ gamma0GreenQuadraticMeasure
    exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  change Integrable _ (Measure.map (gamma0GreenEnergyCoordinate N) (μ.restrict U))
  rw [integrable_map_measure (spectralStieltjesKernel_measurable z).aestronglyMeasurable
    (gamma0GreenEnergyCoordinate_measurable N).aemeasurable]
  apply hf.integrableOn.congr
  filter_upwards [ae_restrict_mem (gamma0GreenPositiveSpectrum_measurable N)] with x hx
  exact gamma0GreenResolventSymbol_eq_energy N z hz x hx

theorem gamma0AmbientResolventFamily_stieltjes (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) (u : Gamma0RegionL2 N) :
    inner ℂ u (gamma0AmbientResolventFamily N z u)=
      ∫ l : ℝ,((l:ℂ)-z)⁻¹ ∂gamma0AmbientSpectralMeasure N u := by
  rw [gamma0AmbientResolventFamily_quadratic_integral N z hz,gamma0AmbientSpectralMeasure,
    integral_map (gamma0GreenEnergyCoordinate_measurable N).aemeasurable
      (spectralStieltjesKernel_measurable z).aestronglyMeasurable]
  let μ := gamma0GreenQuadraticMeasure N u
  let U := gamma0GreenPositiveSpectrum N
  let f := gamma0GreenResolventSymbol N z hz
  change (∫ x,f x ∂μ)=∫ x in U,((gamma0GreenEnergyCoordinate N x:ℂ)-z)⁻¹ ∂μ
  calc
    _ = ∫ x in U,f x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (gamma0GreenResolventSymbol_zero_outside N z hz)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (gamma0GreenPositiveSpectrum_measurable N)] with x hx
      exact gamma0GreenResolventSymbol_eq_energy N z hz x hx

end ArtinMatthews
