module

public import ArtinMatthews.SpectralAmbientEnergyEigenspace
public import ArtinMatthews.SpectralRealEulerTailEnergy
public import ArtinMatthews.SpectralCompactResolventOutgoingMode


set_option backward.privateInPublic true
@[expose] public section

/-! An actual full-energy eigenvector at or above the continuous threshold
has vanishing constant term at all heights of every cusp. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0GlobalCuspConstantTermDerivative_integrable_sq (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (u : gamma0EnergySpace N) (Y : ℝ) (hY : 0<Y) :
    IntegrableOn (fun y => ‖gamma0GlobalCuspConstantTermDerivative N r u y‖^2) (Ioi Y) := by
  have hN : 0<(N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hI := cuspVerticalL2_integrable_energy hN hY (gamma0CuspVerticalConstantTerm N r Y hY u)
  have hAE := (spectralCuspVerticalL2_ae_iff hN hY).mp (gamma0GlobalCuspConstantTermDerivative_ae N r u Y hY)
  apply hI.congr
  filter_upwards [hAE,ae_restrict_mem (μ:=volume) measurableSet_Ioi] with y hD hy
  have hy0 := hY.trans hy
  change ‖gamma0CuspVerticalConstantTerm N r Y hY u y‖^2/y^2=
    ‖gamma0GlobalCuspConstantTermDerivative N r u y‖^2
  rw [hD,gamma0CuspConstantTermDerivative,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hy0.le),mul_pow,inv_pow]
  ring

theorem spectralComplexEulerTail_eq_zero {Y l : ℝ} (hY : 0<Y) (hl : (1/4:ℝ)≤l)
    (c g : ℝ → ℂ) (hc : ∀ y>Y,HasDerivAt c (g y) y)
    (hg : ∀ y>Y,HasDerivAt g (-(l:ℂ)*c y/(y:ℂ)^2) y)
    (hmc : IntegrableOn (fun y => ‖c y‖^2/y^2) (Ioi Y))
    (hmg : IntegrableOn (fun y => ‖g y‖^2) (Ioi Y)) : ∀ y>Y,c y=0 := by
  have hcoord (L : ℂ →L[ℝ] ℝ) (hL : ∀ z,|L z| ≤ ‖z‖) :
      ∀ y>Y,L (c y)=0 := by
    let C := fun y => L (c y)
    let G := fun y => L (g y)
    have hC (y : ℝ) (hy : Y<y) : HasDerivAt C (G y) y :=
      L.hasFDerivAt.comp_hasDerivAt y (hc y hy)
    have hG (y : ℝ) (hy : Y<y) : HasDerivAt G (-l*C y/y^2) y := by
      have he : -(l:ℂ)*c y/(y:ℂ)^2=(-l/y^2:ℝ) • c y := by
        simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_pow]
        ring
      have hd := L.hasFDerivAt.comp_hasDerivAt y (hg y hy)
      change HasDerivAt G (L (-(l:ℂ)*c y/(y:ℂ)^2)) y at hd
      rw [he,map_smul,smul_eq_mul,div_mul_eq_mul_div] at hd
      exact hd
    have hCc : ContinuousOn C (Ioi Y) := fun y hy => (hC y hy).continuousAt.continuousWithinAt
    have hGc : ContinuousOn G (Ioi Y) := fun y hy => (hG y hy).continuousAt.continuousWithinAt
    have hCa : ContinuousOn (fun y => (C y)^2/y^2) (Ioi Y) :=
      (hCc.pow 2).div (continuous_id.continuousOn.pow 2) fun y hy =>
        pow_ne_zero 2 (hY.trans hy).ne'
    have hs (z : ℂ) : (L z)^2≤‖z‖^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (L z)) (hL z) 2
    have hCi : IntegrableOn (fun y => (C y)^2/y^2) (Ioi Y) := by
      apply hmc.mono' (hCa.aestronglyMeasurable measurableSet_Ioi)
      exact ae_of_all _ fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact div_le_div_of_nonneg_right (hs (c y)) (sq_nonneg y)
    have hGi : IntegrableOn (fun y => (G y)^2) (Ioi Y) := by
      apply hmg.mono' ((hGc.pow 2).aestronglyMeasurable measurableSet_Ioi)
      exact ae_of_all _ fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact hs (g y)
    exact spectralRealEulerTail_eq_zero hY hl C G hC hG hCi hGi
  intro y hy
  apply Complex.ext
  · exact hcoord Complex.reCLM Complex.abs_re_le_norm y hy
  · exact hcoord Complex.imCLM Complex.abs_im_le_norm y hy

theorem gamma0EnergyMass_constant_zero_of_critical_eigen (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (l : ℝ) (hl : (1/4:ℝ)≤l) (u : gamma0EnergySpace N)
    (hu : gamma0EnergyResolventPencil N (l:ℂ) u=0) (Y : ℝ) (hY : 0<Y) :
    gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)=ᵐ[volume.restrict (Ioi Y)] 0 := by
  let m := gamma0EnergyInclusion N u
  let c := gamma0GlobalCuspConstantTerm N r m
  let g := gamma0GlobalCuspConstantTermDerivative N r u
  have hsub : Ioi Y⊆Ioi (0:ℝ) := fun _ hy => hY.trans hy
  have hp : gamma0EnergyResolventPencil N (l:ℂ) u=gamma0EnergyMassAdjoint N 0 := by simpa only [map_zero]
  obtain ⟨C,G,_,_,hcC,hgG,hC,hG⟩ := cuspRayWeakEuler_exists_classical hY.le (l:ℂ) c g
    ((gamma0GlobalCuspConstantTerm_locallyIntegrable N r m).mono_set hsub)
    ((gamma0GlobalCuspConstantTermDerivative_locallyIntegrable N r u).mono_set hsub)
    (gamma0EnergyMass_global_constant_first_weak N r u hY)
    (gamma0EnergyMass_global_constant_derivative_weak_of_pencil N r (l:ℂ) u 0 hp Y hY
      (fun ψ _ => inner_zero_right _))
  have hCi : IntegrableOn (fun y => ‖C y‖^2/y^2) (Ioi Y) :=
    (gamma0GlobalCuspConstantTerm_integrable_energy N r m Y hY).congr
      (hcC.mono fun y hy => congrArg (fun x : ℂ => ‖x‖^2/y^2) hy)
  have hGi : IntegrableOn (fun y => ‖G y‖^2) (Ioi Y) :=
    (gamma0GlobalCuspConstantTermDerivative_integrable_sq N r u Y hY).congr
      (hgG.mono fun _ hy => congrArg (fun x : ℂ => ‖x‖^2) hy)
  have hzero := spectralComplexEulerTail_eq_zero hY hl C G hC hG hCi hGi
  filter_upwards [hcC,ae_restrict_mem (μ:=volume) measurableSet_Ioi] with y he hy
  exact he.trans (hzero y hy)

theorem gamma0AmbientEnergyEigenspace_cuspidal_of_critical (N : ℕ) [NeZero N]
    (l : ℝ) (hl : (1/4:ℝ)≤l) (m : Gamma0RegionL2 N) (hm : m∈gamma0AmbientEnergyEigenspace N l) :
    m∈gamma0AllHeightCuspidalMassSpace N := by
  obtain ⟨u,hu,hp⟩ := gamma0AmbientEnergyEigenspace_energy_pencil N l (by linarith) m hm
  rw [← hu,mem_gamma0AllHeightCuspidalMassSpace_iff_globalConstantTerm]
  intro r
  have hN : 0<(N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  apply spectralCuspWeightedGluing_unique hN
  intro n
  have hn := spectralCuspGluingHeight_pos n
  exact (spectralCuspVerticalL2_ae_iff hN hn).mpr
    (gamma0EnergyMass_constant_zero_of_critical_eigen N r l hl u hp _ hn)

theorem gamma0NoncuspidalRemainder_atom_zero_of_critical (N : ℕ) [NeZero N]
    (l : ℝ) (hl : (1/4:ℝ)≤l) (m : Gamma0RegionL2 N) :
    gamma0NoncuspidalRemainder N (gamma0AmbientSpectralAtomVector N m l)=0 := by
  let a := gamma0AmbientSpectralAtomVector N m l
  have ha : a∈gamma0AmbientEnergyEigenspace N l :=
    (mem_gamma0AmbientEnergyEigenspace_iff N l a).mpr (gamma0AmbientSpectralAtomVector_green N m l)
  have hc := gamma0AmbientEnergyEigenspace_cuspidal_of_critical N l hl a ha
  change a-(gamma0AllHeightCuspidalMassSpace N).starProjection a=0
  rw [Submodule.starProjection_eq_self_iff.mpr hc,sub_self]

end ArtinMatthews
