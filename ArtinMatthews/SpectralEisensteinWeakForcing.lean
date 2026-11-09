module

public import ArtinMatthews.SpectralEisensteinRemainderEnergy
public import ArtinMatthews.SpectralEisensteinCutoffAutomorphy
public import ArtinMatthews.SpectralSectionC2Green
public import ArtinMatthews.SpectralGamma0GlobalDifferentialForm
public import ArtinMatthews.SpectralGamma0MassRepresentativeUnfolding
public import ArtinMatthews.SpectralEisensteinSpectralParameter


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ambient weak forcing and resolvent agreement of the original
convergent Eisenstein series. Every forcing and form-domain input is constructed. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem h2CompactInner_integrable (ψ : h2SmoothCompactSeeds) (F : UpperHalfPlane → ℂ)
    (hF : Continuous F) : Integrable (fun z => inner ℂ (ψ.val z) (F z)) := by
  apply (ψ.val.continuous.inner hF).integrable_of_hasCompactSupport
  apply ψ.val.hasCompactSupport.mono'
  intro z hz
  by_contra hn
  exact hz (by
    change inner ℂ (ψ.val z) (F z)=0
    rw [image_eq_zero_of_notMem_tsupport hn,inner_zero_left])

theorem gamma0CuspEisensteinRemainderEnergy_test_forcing (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EnergyGradient N (gamma0EnergyTest N ψ))
        (gamma0EnergyGradient N (gamma0CuspEisensteinRemainderEnergy N a s hs))-
      (s*(1-s))*inner ℂ (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))
        (gamma0CuspEisensteinRemainderMass N a s hs)=
      inner ℂ (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))
        (-gamma0CuspEisensteinCompactForcingMass N a s) := by
  let R := gamma0CuspEisensteinRemainder N a s
  let H := gamma0CuspEisensteinCompactForcing N a s
  have hR : Continuous R := gamma0CuspEisensteinRemainder_continuous N a s hs
  have hH : Continuous H := gamma0CuspEisensteinCompactForcing_continuous N a s
  have hRC2 : ContDiffOn ℝ 2 (fun z : ℂ => R (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    (gamma0CuspEisenstein_spatial_C2 N a s hs).sub
      ((gamma0CuspEisensteinCutoff_spatial_smooth N a s).of_le (by simp))
  have htrans := h2Section_laplacian_transfer_C2 ψ R hRC2
  have hpoint (z : UpperHalfPlane) : h2SectionPositiveLaplacian R z=(s*(1-s))*R z-H z := by
    have h := gamma0CuspEisensteinRemainder_classical_forcing N a s hs z
    change h2SectionPositiveLaplacian R z-(s*(1-s))*R z= -H z at h
    linear_combination h
  have hipoint (z : UpperHalfPlane) : inner ℂ (ψ.val z) (h2SectionPositiveLaplacian R z)=
      (s*(1-s))*inner ℂ (ψ.val z) (R z)-inner ℂ (ψ.val z) (H z) := by
    rw [hpoint,inner_sub_right]
    exact congrArg (fun w : ℂ => w-inner ℂ (ψ.val z) (H z))
      (inner_smul_right (𝕜 := ℂ) (E := ℂ) (ψ.val z) (R z) (s*(1-s)))
  simp_rw [hipoint] at htrans
  rw [integral_sub (h2CompactInner_integrable ψ R hR |>.const_mul (s*(1-s)))
    (h2CompactInner_integrable ψ H hH),integral_const_mul] at htrans
  have hpair := gamma0Energy_completed_global_differential_pairing N ψ
    (gamma0CuspEisensteinRemainderEnergy N a s hs)
  rw [gamma0Energy_inner,gamma0EnergyInclusion_test,gamma0CuspEisensteinRemainderEnergy_mass,
    inner_add_left] at hpair
  have hg := add_left_cancel hpair
  have hψR := gamma0Mass_inner_unfold_representative N (gamma0CuspEisensteinRemainderMass N a s hs)
    R hR (gamma0CuspEisensteinRemainder_automorphy N a s)
    (gamma0CuspEisensteinRemainderMass_ae N a s hs) ψ
  have hΔψR := gamma0Mass_inner_unfold_representative N (gamma0CuspEisensteinRemainderMass N a s hs)
    R hR (gamma0CuspEisensteinRemainder_automorphy N a s)
    (gamma0CuspEisensteinRemainderMass_ae N a s hs) (h2SectionLaplacianSeed ψ)
  have hψH := gamma0Mass_inner_unfold_representative N (gamma0CuspEisensteinCompactForcingMass N a s)
    H hH (gamma0CuspEisensteinCompactForcing_automorphy N a s)
    (gamma0CuspEisensteinCompactForcingMass_ae N a s) ψ
  rw [gamma0EnergyInclusion_test,inner_neg_right,hg,hψR,hΔψR,hψH]
  change (2:ℂ)*(∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (R z))-
    (s*(1-s))*(2*(∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (R z)))=
      -(2*(∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (H z)))
  linear_combination (2:ℂ)*htrans

theorem gamma0CuspEisensteinRemainderEnergy_forcing (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0CuspEisensteinRemainderEnergy N a s hs))-
      (s*(1-s))*inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinRemainderMass N a s hs)=
      inner ℂ (gamma0EnergyInclusion N v) (-gamma0CuspEisensteinCompactForcingMass N a s) := by
  have hA : Continuous (fun v : gamma0EnergySpace N =>
      inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0CuspEisensteinRemainderEnergy N a s hs))-
      (s*(1-s))*inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinRemainderMass N a s hs)) :=
    ((gamma0EnergyGradient N).continuous.inner continuous_const).sub
      (((gamma0EnergyInclusion N).continuous.inner continuous_const).const_mul (s*(1-s)))
  have hB : Continuous (fun v : gamma0EnergySpace N =>
      inner ℂ (gamma0EnergyInclusion N v) (-gamma0CuspEisensteinCompactForcingMass N a s)) :=
    (gamma0EnergyInclusion N).continuous.inner continuous_const
  have hall : ∀ v : gamma0EnergySpace N,
      inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0CuspEisensteinRemainderEnergy N a s hs))-
      (s*(1-s))*inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinRemainderMass N a s hs)=
      inner ℂ (gamma0EnergyInclusion N v) (-gamma0CuspEisensteinCompactForcingMass N a s) := by
    apply isClosed_property (gamma0EnergyTest_dense N) (isClosed_eq hA hB)
    intro ψ
    exact gamma0CuspEisensteinRemainderEnergy_test_forcing N a s hs ψ
  exact hall v

theorem gamma0CuspEisensteinRemainderEnergy_resolvent (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    gamma0CuspEisensteinRemainderEnergy N a s hs=
      gamma0AmbientWeakResolvent N (s*(1-s)) (eisensteinSpectralParameter_off_nonnegative_ray s hs)
        (-gamma0CuspEisensteinCompactForcingMass N a s) := by
  apply gamma0AmbientWeakResolvent_unique
  intro v
  rw [gamma0CuspEisensteinRemainderEnergy_mass]
  exact gamma0CuspEisensteinRemainderEnergy_forcing N a s hs v

theorem gamma0CuspEisensteinRemainderMass_resolvent (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    gamma0CuspEisensteinRemainderMass N a s hs=
      gamma0AmbientResolvent N (s*(1-s)) (eisensteinSpectralParameter_off_nonnegative_ray s hs)
        (-gamma0CuspEisensteinCompactForcingMass N a s) := by
  have h := congrArg (gamma0EnergyInclusion N) (gamma0CuspEisensteinRemainderEnergy_resolvent N a s hs)
  rw [gamma0CuspEisensteinRemainderEnergy_mass] at h
  exact h

end ArtinMatthews
