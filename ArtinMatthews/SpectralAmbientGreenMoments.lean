module

public import ArtinMatthews.SpectralAmbientSpectralAtoms


set_option backward.privateInPublic true
@[expose] public section

/-! Exact moments of the actual scalar energy spectral measure,
obtained from the original positive Green functional calculus. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0EnergyGreenWeight (l : ℝ) : ℂ := ((l:ℂ)+1)⁻¹

theorem gamma0EnergyGreenWeight_measurable : Measurable gamma0EnergyGreenWeight :=
  (Complex.measurable_ofReal.add_const 1).inv

theorem gamma0EnergyGreenWeight_eq_real (l : ℝ) :
    gamma0EnergyGreenWeight l=(((l+1)⁻¹:ℝ):ℂ) := by
  rw [gamma0EnergyGreenWeight,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one]

theorem gamma0EnergyGreenWeight_coordinate (N : ℕ) [NeZero N]
    (x : spectrum ℂ (gamma0Green N)) :
    gamma0EnergyGreenWeight (gamma0GreenEnergyCoordinate N x)=(x:ℂ) := by
  obtain ⟨r,_,_,hr⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  rw [gamma0EnergyGreenWeight_eq_real,gamma0GreenEnergyCoordinate,hr,Complex.ofReal_re,sub_add_cancel,inv_inv]

theorem gamma0GreenSpectrumCoordinate_zero_compl (N : ℕ) [NeZero N]
    (x : spectrum ℂ (gamma0Green N)) (hx : x∉gamma0GreenPositiveSpectrum N) : (x:ℂ)=0 := by
  obtain ⟨r,hr,_,he⟩ := gamma0Green_spectrum_complex_mem_real_unit N x.property
  change ¬0<(x:ℂ).re at hx
  rw [he,Complex.ofReal_re] at hx
  have hz : r=0 := le_antisymm (le_of_not_gt hx) hr
  rw [he,hz,Complex.ofReal_zero]

theorem gamma0AmbientSpectralMeasure_green_power_integrable (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (n : ℕ) :
    Integrable (fun l => gamma0EnergyGreenWeight l^n) (gamma0AmbientSpectralMeasure N u) := by
  let μ := gamma0GreenQuadraticMeasure N u
  let U := gamma0GreenPositiveSpectrum N
  let _ : IsFiniteMeasure μ := by
    dsimp only [μ,gamma0GreenQuadraticMeasure]
    infer_instance
  have hi : Integrable (fun x : spectrum ℂ (gamma0Green N) => (x:ℂ)^n) μ :=
    ((continuous_subtype_val.pow n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [gamma0AmbientSpectralMeasure,integrable_map_measure
    ((gamma0EnergyGreenWeight_measurable.pow_const n).aestronglyMeasurable)
    (gamma0GreenEnergyCoordinate_measurable N).aemeasurable]
  exact hi.integrableOn.congr (ae_of_all _ (fun x => congrArg (fun z : ℂ => z^n)
    (gamma0EnergyGreenWeight_coordinate N x).symm))

theorem gamma0AmbientSpectralMeasure_green_power (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (n : ℕ) (hn : n≠0) :
    (∫ l,gamma0EnergyGreenWeight l^n ∂gamma0AmbientSpectralMeasure N u)=
      inner ℂ u (((gamma0Green N)^n) u) := by
  let μ := gamma0GreenQuadraticMeasure N u
  let U := gamma0GreenPositiveSpectrum N
  rw [gamma0AmbientSpectralMeasure,integral_map (gamma0GreenEnergyCoordinate_measurable N).aemeasurable
    (gamma0EnergyGreenWeight_measurable.pow_const n).aestronglyMeasurable]
  change (∫ x in U,gamma0EnergyGreenWeight (gamma0GreenEnergyCoordinate N x)^n ∂μ)=_
  simp_rw [gamma0EnergyGreenWeight_coordinate]
  calc
    _ = ∫ x : spectrum ℂ (gamma0Green N),(x:ℂ)^n ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [gamma0GreenSpectrumCoordinate_zero_compl N x hx,zero_pow hn])
    _ = _ := by
      have h := spectralQuadraticMeasure_integral_complex (gamma0Green N)
        (gamma0Green_selfAdjoint N).isStarNormal u ((gamma0GreenSpectrumCoordinate N)^n)
      have hid : cfcHom (gamma0Green_selfAdjoint N).isStarNormal
          (gamma0GreenSpectrumCoordinate N)=gamma0Green N := cfcHom_id _
      rw [map_pow,hid] at h
      exact h

theorem gamma0AmbientSpectralMeasure_green_first_moment (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    (∫ l,gamma0EnergyGreenWeight l ∂gamma0AmbientSpectralMeasure N u)=inner ℂ u (gamma0Green N u) := by
  simpa only [pow_one] using gamma0AmbientSpectralMeasure_green_power N u 1 (by decide)

theorem gamma0AmbientSpectralMeasure_green_second_moment (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    (∫ l,gamma0EnergyGreenWeight l^2 ∂gamma0AmbientSpectralMeasure N u)=((‖gamma0Green N u‖^2:ℝ):ℂ) := by
  rw [gamma0AmbientSpectralMeasure_green_power N u 2 (by decide),pow_two,mul_apply_eq_comp]
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0Green_selfAdjoint N)) u (gamma0Green N u)
  change inner ℂ (gamma0Green N u) (gamma0Green N u)=inner ℂ u (gamma0Green N (gamma0Green N u)) at h
  rw [← h,inner_self_eq_norm_sq_to_K (𝕜:=ℂ),Complex.ofReal_pow]
  rfl

end ArtinMatthews
