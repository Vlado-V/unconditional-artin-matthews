module

public import ArtinMatthews.SpectralCompactResolventCuspSupport
public import ArtinMatthews.SpectralEisensteinTailWeakSystem


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine full energy solution with forcing supported below a cusp
cutoff satisfies the homogeneous weak Euler equation for its high mean. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews
open SpectralCuspRayRegularity

theorem gamma0EnergyMass_global_weak_laplacian_of_pencil (N : ℕ) [NeZero N]
    (z : ℂ) (u : gamma0EnergySpace N) (F : Gamma0RegionL2 N)
    (hu : gamma0EnergyResolventPencil N z u=gamma0EnergyMassAdjoint N F)
    (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) (gamma0EnergyInclusion N u)-
      z*inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0EnergyInclusion N u)=
        inner ℂ (gamma0SmoothSeedMass N ψ) F := by
  have h := congrArg (fun v : gamma0EnergySpace N => inner ℂ (gamma0EnergyTest N ψ) v) hu
  change inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyResolventPencil N z u)=
    inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyMassAdjoint N F) at h
  rwa [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner,
    gamma0EnergyGradient_completed_differential_pairing,gamma0EnergyInclusion_test] at h

theorem gamma0EnergyMass_constant_second_weak_of_pencil (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (z : ℂ) (u : gamma0EnergySpace N) (F : Gamma0RegionL2 N)
    (hu : gamma0EnergyResolventPencil N z u=gamma0EnergyMassAdjoint N F)
    (Y : ℝ) (hY : 0<Y)
    (hF : ∀ ψ : h2SmoothCompactSeeds,
      (∀ p∈Function.support (fun p : UpperHalfPlane => ψ.val p),Y<p.im) →
      inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ)) F=0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ y in Ioi Y, deriv (deriv ρ) y • gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N u) y)=
      -z*(∫ y in Ioi Y, (ρ y/y^2) • gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N u) y) := by
  let hpos : tsupport ρ ⊆ Ioi (0:ℝ) := fun _ hy => hY.trans (hρs hy)
  let ψ := cuspConstantTermTestSeed (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hpos
  have hψ := cuspConstantTermTestSeed_support (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hpos Y hρs
  have hΔψ := cuspConstantTermTestSeed_laplacian_support (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hpos Y hρs
  have he := gamma0EnergyMass_global_weak_laplacian_of_pencil N z u F hu (modularTranslateSmoothSeed r ψ)
  rw [hF ψ (fun p hp => (hψ hp).2),h2SectionLaplacianSeed_modular_pullback,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ,
    gamma0CuspTwoCellMassRestriction_test_pairing,
    gamma0CuspTwoCellMassRestriction_laplacian_pairing] at he
  simp only [Complex.real_smul] at he
  have hN : (N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) hN))
  linear_combination -he

theorem gamma0EnergyMass_global_constant_first_weak (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (u : gamma0EnergySpace N) {Y : ℝ} (hY : 0<Y) :
    RayWeakDerivative (Y:=Y) (gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u))
      (gamma0GlobalCuspConstantTermDerivative N r u) := by
  intro ρ hρ hρc hρs
  have hρpos : tsupport ρ⊆Ioi (0:ℝ) := fun _ hy => hY.trans (hρs hy)
  have he := gamma0GlobalCuspConstantTerm_weak_derivative N r u ρ hρ hρc hρpos
  rw [spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi (0:ℝ)) (tsupport_deriv_subset.trans hρpos),
    spectralTest_setIntegral_eq_integral ρ (Ioi (0:ℝ)) hρpos] at he
  rw [ray_test_setIntegral_eq _ (tsupport_deriv_subset.trans hρs),ray_test_setIntegral_eq _ hρs]
  exact he

theorem gamma0EnergyMass_global_constant_derivative_weak_of_pencil (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (z : ℂ) (u : gamma0EnergySpace N) (F : Gamma0RegionL2 N)
    (hu : gamma0EnergyResolventPencil N z u=gamma0EnergyMassAdjoint N F)
    (Y : ℝ) (hY : 0<Y)
    (hF : ∀ ψ : h2SmoothCompactSeeds,
      (∀ p∈Function.support (fun p : UpperHalfPlane => ψ.val p),Y<p.im) →
      inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ)) F=0) :
    RayWeakDerivative (Y:=Y) (gamma0GlobalCuspConstantTermDerivative N r u)
      (fun y => -z*gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u) y/(y:ℂ)^2) := by
  intro ρ hρ hρc hρs
  let c := gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
  let C := gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N u)
  have hae : c=ᵐ[volume.restrict (Ioi Y)] C :=
    (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
      (gamma0GlobalCuspConstantTerm_ae N r (gamma0EnergyInclusion N u) Y hY)
  have hl : (∫ y in Ioi Y, deriv (deriv ρ) y • c y)=∫ y in Ioi Y, deriv (deriv ρ) y • C y :=
    integral_congr_ae (hae.mono fun y hy => congrArg (fun x : ℂ => deriv (deriv ρ) y • x) hy)
  have hr : (∫ y in Ioi Y, (ρ y/y^2) • c y)=∫ y in Ioi Y, (ρ y/y^2) • C y :=
    integral_congr_ae (hae.mono fun y hy => congrArg (fun x : ℂ => (ρ y/y^2) • x) hy)
  have he : (∫ y in Ioi Y, deriv (deriv ρ) y • c y)=-z*(∫ y in Ioi Y, (ρ y/y^2) • c y) :=
    hl.trans ((gamma0EnergyMass_constant_second_weak_of_pencil N r z u F hu Y hY hF ρ hρ hρc hρs).trans
      (congrArg (fun x : ℂ => -z*x) hr.symm))
  have hd := gamma0EnergyMass_global_constant_first_weak N r u hY
    (deriv ρ) (contDiff_infty_iff_deriv.mp hρ).2 hρc.deriv (tsupport_deriv_subset.trans hρs)
  have hi (y : ℝ) : ρ y • (-z*c y/(y:ℂ)^2)=-z*((ρ y/y^2) • c y) := by
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow]
    ring
  change (∫ y in Ioi Y,deriv ρ y • gamma0GlobalCuspConstantTermDerivative N r u y)=
    -(∫ y in Ioi Y,ρ y • (-z*c y/(y:ℂ)^2))
  simp_rw [hi]
  rw [integral_const_mul]
  linear_combination hd-he

end ArtinMatthews
