module

public import ArtinMatthews.SpectralEisensteinCutoffCompactTesting
public import ArtinMatthews.SpectralEisensteinProfileMajorants


set_option backward.privateInPublic true
@[expose] public section

/-! An actual smooth invariant representative and its literal compact
forcing identify the full completed energy equation via the dense core. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0Energy_pencil_of_classical_forcing (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (ζ : ℂ) (M : Gamma0RegionL2 N)
    (F H : UpperHalfPlane → ℂ) (hF : Continuous F) (hH : Continuous H)
    (hF2 : ContDiffOn ℝ 2 (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0<z.im})
    (hFinv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (g.val • z)=F z)
    (hHinv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, H (g.val • z)=H z)
    (hFu : ∀ i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      (gamma0EnergyInclusion N u i : UpperHalfPlane → ℂ)=ᵐ[volume.restrict ModularGroup.fd]
        fun z => F (i.out⁻¹ • z))
    (hHM : ∀ i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      (M i : UpperHalfPlane → ℂ)=ᵐ[volume.restrict ModularGroup.fd] fun z => H (i.out⁻¹ • z))
    (hPoint : ∀ z, h2SectionPositiveLaplacian F z-ζ*F z=H z) :
    gamma0EnergyResolventPencil N ζ u=gamma0EnergyMassAdjoint N M := by
  apply ext_inner_left ℂ
  intro v
  have hall : ∀ v : gamma0EnergySpace N, inner ℂ v (gamma0EnergyResolventPencil N ζ u)=
      inner ℂ v (gamma0EnergyMassAdjoint N M) := by
    have hL : Continuous (fun w : gamma0EnergySpace N => inner ℂ w (gamma0EnergyResolventPencil N ζ u)) :=
      (innerSLFlip ℂ (gamma0EnergyResolventPencil N ζ u)).continuous
    have hR : Continuous (fun w : gamma0EnergySpace N => inner ℂ w (gamma0EnergyMassAdjoint N M)) :=
      (innerSLFlip ℂ (gamma0EnergyMassAdjoint N M)).continuous
    apply isClosed_property (gamma0EnergyTest_dense N) (isClosed_eq hL hR)
    intro ψ
    change inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyResolventPencil N ζ u)=
      inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyMassAdjoint N M)
    have hpair := gamma0Energy_completed_global_differential_pairing N ψ u
    rw [gamma0Energy_inner,gamma0EnergyInclusion_test,inner_add_left] at hpair
    have hg := add_left_cancel hpair
    have htrans := h2Section_laplacian_transfer_C2 ψ F hF2
    have hp (z : UpperHalfPlane) : inner ℂ (ψ.val z) (h2SectionPositiveLaplacian F z)=
        ζ*inner ℂ (ψ.val z) (F z)+inner ℂ (ψ.val z) (H z) := by
      have he := hPoint z
      have he' : h2SectionPositiveLaplacian F z=ζ*F z+H z := by linear_combination he
      rw [he',inner_add_right]
      exact congrArg (fun w : ℂ => w+inner ℂ (ψ.val z) (H z))
        (inner_smul_right (𝕜 := ℂ) (E := ℂ) (ψ.val z) (F z) ζ)
    simp_rw [hp] at htrans
    rw [integral_add ((h2CompactInner_integrable ψ F hF).const_mul ζ)
      (h2CompactInner_integrable ψ H hH),integral_const_mul] at htrans
    rw [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner,gamma0EnergyInclusion_test,hg,
      gamma0Mass_inner_unfold_representative N (gamma0EnergyInclusion N u) F hF hFinv hFu ψ,
      gamma0Mass_inner_unfold_representative N (gamma0EnergyInclusion N u) F hF hFinv hFu (h2SectionLaplacianSeed ψ),
      gamma0Mass_inner_unfold_representative N M H hH hHinv hHM ψ]
    change (2:ℂ)*(∫ z : UpperHalfPlane,inner ℂ (h2SectionPositiveLaplacian ψ.val z) (F z))-
      ζ*(2*∫ z : UpperHalfPlane,inner ℂ (ψ.val z) (F z))=
      2*∫ z : UpperHalfPlane,inner ℂ (ψ.val z) (H z)
    linear_combination (2:ℂ)*htrans
  exact hall v

theorem gamma0CuspCompactHeightProfile_spatial_smooth (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hpos : tsupport ρ⊆Ioi (0:ℝ)) :
    ContDiffOn ℝ ∞ (fun z : ℂ => gamma0CuspHeightProfile N a ρ (UpperHalfPlane.ofComplex z))
      {z | 0<z.im} := by
  let ψ := cuspHeightProfileSeed N a ρ hρ hρc hpos
  have he : gamma0CuspHeightProfile N a ρ =
      fun z => (1/2:ℂ)*gamma0PoincareSeed N ψ.val z :=
    funext (gamma0CuspHeightProfile_eq_poincare N a ρ hρ hρc hpos)
  rw [he]
  exact contDiffOn_const.mul (gamma0PoincareSeed_smooth N ψ.val ψ.property)

theorem gamma0CuspHeightProfile_sub_of_zero_low (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (f g : ℝ → ℂ) {ε : ℝ} (hε : 0<ε) (hf : ∀ t≤ε,f t=0) (hg : ∀ t≤ε,g t=0)
    (z : UpperHalfPlane) :
    gamma0CuspHeightProfile N a (fun t => f t-g t) z=
      gamma0CuspHeightProfile N a f z-gamma0CuspHeightProfile N a g z := by
  have hF : Summable (fun v : Gamma0CuspEisensteinRows N 1 a => f (cuspEisensteinNormalizedHeight N 1 a v z)) :=
    summable_of_hasFiniteSupport
    (cuspEisensteinProfile_hasFiniteSupport N 1 a f hε hf z)
  have hG : Summable (fun v : Gamma0CuspEisensteinRows N 1 a => g (cuspEisensteinNormalizedHeight N 1 a v z)) :=
    summable_of_hasFiniteSupport
    (cuspEisensteinProfile_hasFiniteSupport N 1 a g hε hg z)
  rw [gamma0CuspHeightProfile_eq_tsum N a _ hε (fun t ht => by rw [hf t ht,hg t ht,sub_self]),
    gamma0CuspHeightProfile_eq_tsum N a f hε hf z,gamma0CuspHeightProfile_eq_tsum N a g hε hg z,
    hF.tsum_sub hG,mul_sub]

end ArtinMatthews
