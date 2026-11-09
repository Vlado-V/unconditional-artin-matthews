module

public import ArtinMatthews.SpectralEisensteinUpperCutoffError
public import ArtinMatthews.SpectralEisensteinClassicalPencil
public import ArtinMatthews.SpectralEisensteinCompactProfileModes


set_option backward.privateInPublic true
@[expose] public section

/-! The compact upper truncation lies in the actual full energy space
at every parameter. Its exact equation is the original forcing minus
the compact forcing in the upper cutoff band. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def gamma0CuspUpperTruncatedEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (A : ℝ) (hA : 0<A) : gamma0EnergySpace N :=
  gamma0CuspHeightProfileEnergy N a (eisensteinOutgoingApprox q A)
    (eisensteinOutgoingApprox_smooth q A) (eisensteinOutgoingApprox_compact q hA)
    (eisensteinOutgoingApprox_positive_support q hA)

def gamma0CuspUpperCutoffForcingMass (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (A : ℝ) (hA : 0<A) : Gamma0RegionL2 N :=
  gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N a (eisensteinUpperCutoffError q A)
    (eisensteinUpperCutoffError_smooth q A) (eisensteinUpperCutoffError_compact q hA)
    (eisensteinUpperCutoffError_positive_support q hA))

theorem gamma0CuspUpperCutoffForcingMass_ae (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (q : ℂ) (A : ℝ) (hA : 0<A) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspUpperCutoffForcingMass N a q A hA i : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd]
        fun z => gamma0CuspHeightProfile N a (eisensteinUpperCutoffError q A) (i.out⁻¹ • z) :=
  gamma0CuspHeightProfileEnergy_mass_ae N a _ _ _ _ i

theorem gamma0CuspUpperTruncatedEnergy_pencil (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (A : ℝ) (hA : 0<A) (hA2 : A≤1/2) :
    gamma0EnergyResolventPencil N (q*(1-q)) (gamma0CuspUpperTruncatedEnergy N a q A hA)=
      gamma0EnergyMassAdjoint N
        (gamma0CuspEisensteinCompactForcingMass N a q-gamma0CuspUpperCutoffForcingMass N a q A hA) := by
  let F := gamma0CuspHeightProfile N a (eisensteinOutgoingApprox q A)
  let Hhi := gamma0CuspHeightProfile N a (eisensteinUpperCutoffError q A)
  let H (z : UpperHalfPlane) := gamma0CuspEisensteinCompactForcing N a q z-Hhi z
  have hFs : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0<z.im} :=
    gamma0CuspCompactHeightProfile_spatial_smooth N a _ (eisensteinOutgoingApprox_smooth q A)
      (eisensteinOutgoingApprox_compact q hA) (eisensteinOutgoingApprox_positive_support q hA)
  have hHi : Continuous Hhi := spectralSection_continuous _
    (gamma0CuspCompactHeightProfile_spatial_smooth N a _ (eisensteinUpperCutoffError_smooth q A)
      (eisensteinUpperCutoffError_compact q hA) (eisensteinUpperCutoffError_positive_support q hA))
  apply gamma0Energy_pencil_of_classical_forcing N _ _ _ F H
    (spectralSection_continuous _ hFs) ((gamma0CuspEisensteinCompactForcing_continuous N a q).sub hHi)
    (hFs.of_le (by simp)) (gamma0CuspHeightProfile_automorphy N a _)
  · intro g z
    change gamma0CuspEisensteinCompactForcing N a q (g.val • z)-Hhi (g.val • z)=_
    rw [gamma0CuspEisensteinCompactForcing_automorphy N a q g z,
      show Hhi (g.val • z)=Hhi z from gamma0CuspHeightProfile_automorphy N a _ g z]
  · intro i
    exact gamma0CuspHeightProfileEnergy_mass_ae N a _ _ _ _ i
  · intro i
    filter_upwards [Lp.coeFn_sub (gamma0CuspEisensteinCompactForcingMass N a q i)
        (gamma0CuspUpperCutoffForcingMass N a q A hA i),
      gamma0CuspEisensteinCompactForcingMass_ae N a q i,
      gamma0CuspUpperCutoffForcingMass_ae N a q A hA i] with z hs hlo hhi
    change ((gamma0CuspEisensteinCompactForcingMass N a q i-gamma0CuspUpperCutoffForcingMass N a q A hA i :
      Lp ℂ 2 (volume.restrict ModularGroup.fd)) : UpperHalfPlane → ℂ) z=_
    rw [hs,Pi.sub_apply,hlo,hhi]
  · intro z
    change h2SectionPositiveLaplacian (gamma0CuspHeightProfile N a (eisensteinOutgoingApprox q A)) z-
      q*(1-q)*gamma0CuspHeightProfile N a (eisensteinOutgoingApprox q A) z=_
    rw [gamma0CuspHeightProfile_laplacian_error N a _ (eisensteinOutgoingApprox_smooth q A) zero_lt_one
      (fun _ ht => eisensteinOutgoingApprox_zero_low q A ht),
      funext (eisensteinOutgoingApprox_radial_error q hA hA2)]
    exact gamma0CuspHeightProfile_sub_of_zero_low N a _ _ (by norm_num : (0:ℝ)<1/2)
      (fun t ht => eisensteinVerticalCutoffError_zero q (Or.inl (by linarith)))
      (fun t ht => eisensteinUpperCutoffError_zero q (Or.inl (by
        have hAt := mul_le_mul_of_nonneg_left ht hA.le
        linarith))) z

theorem gamma0CuspUpperTruncatedEnergy_constant_mode (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (q : ℂ) (A : ℝ) (hA : 0<A) (Y : ℝ) (hY : 0<Y) (hhigh : (gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N (gamma0CuspUpperTruncatedEnergy N a q A hA))
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
      fun y => gamma0CuspEisensteinIndicator N r a*eisensteinOutgoingApprox q A (y/(gamma0CuspTrueWidth N r:ℝ)) :=
  gamma0CuspCompactHeightProfile_constant_mode N r a _ (eisensteinOutgoingApprox_smooth q A)
    (eisensteinOutgoingApprox_compact q hA) (eisensteinOutgoingApprox_positive_support q hA)
    (fun _ ht => eisensteinOutgoingApprox_zero_low q A ht) Y hY hhigh

end ArtinMatthews
