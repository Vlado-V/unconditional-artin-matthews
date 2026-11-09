module

public import ArtinMatthews.SpectralEisensteinOutgoingEnergy
public import ArtinMatthews.SpectralEisensteinWeakForcing
public import ArtinMatthews.SpectralAmbientResolventOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The actual outgoing cutoff satisfies the exact positive compact-forcing
equation on the full ambient form domain. The graph theorem also holds at
spectral parameters where no ambient resolvent is invoked. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspOutgoingCutoffEnergy_test_forcing (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EnergyGradient N (gamma0EnergyTest N ψ))
        (gamma0EnergyGradient N (gamma0CuspOutgoingCutoffEnergy N a q hq))-
      (q*(1-q))*inner ℂ (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))
        (gamma0CuspOutgoingCutoffMass N a q hq)=
      inner ℂ (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))
        (gamma0CuspEisensteinCompactForcingMass N a q) := by
  let C := gamma0CuspEisensteinCutoff N a q
  let H := gamma0CuspEisensteinCompactForcing N a q
  have hC : Continuous C := gamma0CuspOutgoingCutoff_continuous N a q
  have hH : Continuous H := gamma0CuspEisensteinCompactForcing_continuous N a q
  have hC2 : ContDiffOn ℝ 2 (fun z : ℂ => C (UpperHalfPlane.ofComplex z)) {z | 0 < z.im} :=
    (gamma0CuspEisensteinCutoff_spatial_smooth N a q).of_le (by simp)
  have htrans := h2Section_laplacian_transfer_C2 ψ C hC2
  have hpoint (z : UpperHalfPlane) : h2SectionPositiveLaplacian C z=(q*(1-q))*C z+H z := by
    have h := gamma0CuspEisensteinCutoff_laplacian_error N a q z
    change h2SectionPositiveLaplacian C z-(q*(1-q))*C z=H z at h
    linear_combination h
  have hipoint (z : UpperHalfPlane) : inner ℂ (ψ.val z) (h2SectionPositiveLaplacian C z)=
      (q*(1-q))*inner ℂ (ψ.val z) (C z)+inner ℂ (ψ.val z) (H z) := by
    rw [hpoint,inner_add_right]
    exact congrArg (fun w : ℂ => w+inner ℂ (ψ.val z) (H z))
      (inner_smul_right (𝕜 := ℂ) (E := ℂ) (ψ.val z) (C z) (q*(1-q)))
  simp_rw [hipoint] at htrans
  rw [integral_add ((h2CompactInner_integrable ψ C hC).const_mul (q*(1-q)))
    (h2CompactInner_integrable ψ H hH),integral_const_mul] at htrans
  have hpair := gamma0Energy_completed_global_differential_pairing N ψ
    (gamma0CuspOutgoingCutoffEnergy N a q hq)
  rw [gamma0Energy_inner,gamma0EnergyInclusion_test,gamma0CuspOutgoingCutoffEnergy_mass,
    inner_add_left] at hpair
  have hg := add_left_cancel hpair
  have hψC := gamma0Mass_inner_unfold_representative N (gamma0CuspOutgoingCutoffMass N a q hq)
    C hC (gamma0CuspEisensteinCutoff_automorphy N a q)
    (gamma0CuspOutgoingCutoffMass_ae N a q hq) ψ
  have hΔψC := gamma0Mass_inner_unfold_representative N (gamma0CuspOutgoingCutoffMass N a q hq)
    C hC (gamma0CuspEisensteinCutoff_automorphy N a q)
    (gamma0CuspOutgoingCutoffMass_ae N a q hq) (h2SectionLaplacianSeed ψ)
  have hψH := gamma0Mass_inner_unfold_representative N (gamma0CuspEisensteinCompactForcingMass N a q)
    H hH (gamma0CuspEisensteinCompactForcing_automorphy N a q)
    (gamma0CuspEisensteinCompactForcingMass_ae N a q) ψ
  rw [gamma0EnergyInclusion_test,hg,hψC,hΔψC,hψH]
  change (2:ℂ)*(∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (C z))-
    (q*(1-q))*(2*(∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (C z)))=
      2*(∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (H z))
  linear_combination (2:ℂ)*htrans

theorem gamma0CuspOutgoingCutoffEnergy_forcing (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0CuspOutgoingCutoffEnergy N a q hq))-
      (q*(1-q))*inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspOutgoingCutoffMass N a q hq)=
      inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinCompactForcingMass N a q) := by
  have hA : Continuous (fun v : gamma0EnergySpace N =>
      inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0CuspOutgoingCutoffEnergy N a q hq))-
      (q*(1-q))*inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspOutgoingCutoffMass N a q hq)) :=
    ((gamma0EnergyGradient N).continuous.inner continuous_const).sub
      (((gamma0EnergyInclusion N).continuous.inner continuous_const).const_mul (q*(1-q)))
  have hB : Continuous (fun v : gamma0EnergySpace N =>
      inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinCompactForcingMass N a q)) :=
    (gamma0EnergyInclusion N).continuous.inner continuous_const
  have hall : ∀ v : gamma0EnergySpace N,
      inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0CuspOutgoingCutoffEnergy N a q hq))-
      (q*(1-q))*inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspOutgoingCutoffMass N a q hq)=
      inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinCompactForcingMass N a q) := by
    apply isClosed_property (gamma0EnergyTest_dense N) (isClosed_eq hA hB)
    intro ψ
    exact gamma0CuspOutgoingCutoffEnergy_test_forcing N a q hq ψ
  exact hall v

theorem gamma0CuspOutgoingCutoffMass_operator_graph (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    (gamma0CuspOutgoingCutoffMass N a q hq,
      gamma0CuspEisensteinCompactForcingMass N a q+
        (q*(1-q)+1) • gamma0CuspOutgoingCutoffMass N a q hq)
      ∈ (gamma0MassEnergyOperator N).graph := by
  let U := gamma0CuspOutgoingCutoffEnergy N a q hq
  let X := gamma0CuspOutgoingCutoffMass N a q hq
  let F := gamma0CuspEisensteinCompactForcingMass N a q
  refine (gamma0MassEnergyOperator_weak_graph N _ _).mpr ⟨U,rfl,fun v => ?_⟩
  have he := gamma0CuspOutgoingCutoffEnergy_forcing N a q hq v
  have hright : inner ℂ v U=inner ℂ (gamma0EnergyInclusion N v) (F+(q*(1-q)+1) • X) := by
    change inner ℂ (gamma0EnergyGradient N v) (gamma0EnergyGradient N U)-
      q*(1-q)*inner ℂ (gamma0EnergyInclusion N v) X=inner ℂ (gamma0EnergyInclusion N v) F at he
    rw [gamma0FormEnergy_inner,gamma0CuspOutgoingCutoffEnergy_mass,inner_add_right,inner_smul_right]
    linear_combination he
  exact (inner_conj_symm (𝕜 := ℂ) U v).symm.trans
    ((congrArg (starRingEnd ℂ) hright).trans (inner_conj_symm (𝕜 := ℂ) _ _))

theorem gamma0CuspOutgoingCutoffEnergy_resolvent (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (hoff : (q*(1-q)).re<‖q*(1-q)‖) :
    gamma0CuspOutgoingCutoffEnergy N a q hq=
      gamma0AmbientWeakResolvent N (q*(1-q)) hoff (gamma0CuspEisensteinCompactForcingMass N a q) := by
  apply gamma0AmbientWeakResolvent_unique
  intro v
  rw [gamma0CuspOutgoingCutoffEnergy_mass]
  exact gamma0CuspOutgoingCutoffEnergy_forcing N a q hq v

theorem gamma0CuspOutgoingCutoffMass_resolvent (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (hoff : (q*(1-q)).re<‖q*(1-q)‖) :
    gamma0CuspOutgoingCutoffMass N a q hq=
      gamma0AmbientResolvent N (q*(1-q)) hoff (gamma0CuspEisensteinCompactForcingMass N a q) := by
  have h := congrArg (gamma0EnergyInclusion N) (gamma0CuspOutgoingCutoffEnergy_resolvent N a q hq hoff)
  rw [gamma0CuspOutgoingCutoffEnergy_mass] at h
  exact h

end ArtinMatthews
