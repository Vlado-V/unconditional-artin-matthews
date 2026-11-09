module

public import ArtinMatthews.SpectralEisensteinCompactCutoff
public import ArtinMatthews.SpectralCuspGraphRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! Complex-linear restriction from the genuine modular chart L² space
to each compact part, with exact identification of the literal cutoffs. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def spectralComplexLpMeasureRestriction {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (h : ν≤μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν where
  toFun := spectralLpMeasureRestriction h
  map_add' := (spectralLpMeasureRestriction h).map_add
  map_smul' c u := by
    apply Lp.ext
    have hs := (Measure.absolutelyContinuous_of_le h).ae_eq (Lp.coeFn_smul c u)
    filter_upwards [spectralLpMeasureRestriction_ae h (c • u),
      spectralLpMeasureRestriction_ae h u,
      Lp.coeFn_smul c (spectralLpMeasureRestriction h u),hs] with x hu hv hm hc
    simp only [RingHom.id_apply]
    rw [hu,hm,hc,Pi.smul_apply,Pi.smul_apply,hv]
  cont := (spectralLpMeasureRestriction h).continuous

theorem spectralComplexLpMeasureRestriction_ae {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (h : ν≤μ) (u : Lp ℂ 2 μ) :
    spectralComplexLpMeasureRestriction h u =ᵐ[ν] u :=
  spectralLpMeasureRestriction_ae h u

def gamma0EisensteinCompactChartRestriction (N : ℕ) [NeZero N]
    (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (K : Set UpperHalfPlane)
    (hsub : K⊆ModularGroup.fd) : Gamma0RegionL2 N →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
  (spectralComplexLpMeasureRestriction (Measure.restrict_mono_set _ hsub)).comp
    (PiLp.proj 2 _ i)

theorem gamma0EisensteinCompactChartRestriction_ae (N : ℕ) [NeZero N]
    (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (K : Set UpperHalfPlane)
    (hsub : K⊆ModularGroup.fd) (u : Gamma0RegionL2 N) :
    gamma0EisensteinCompactChartRestriction N i K hsub u =ᵐ[volume.restrict K] u i :=
  spectralComplexLpMeasureRestriction_ae (Measure.restrict_mono_set _ hsub) (u i)

theorem gamma0CuspOutgoingCutoffMass_compact_restriction (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hsub : K⊆ModularGroup.fd) :
    gamma0EisensteinCompactChartRestriction N i K hsub (gamma0CuspOutgoingCutoffMass N a q hq)=
      gamma0CuspEisensteinCutoffCompactMass N a i.out K hK q := by
  apply Lp.ext
  exact (gamma0EisensteinCompactChartRestriction_ae N i K hsub _).trans
    (((Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set _ hsub)).ae_eq
      (gamma0CuspOutgoingCutoffMass_ae N a q hq i)).trans
      (gamma0CuspEisensteinCutoffCompactMass_ae N a i.out K hK q).symm)

end ArtinMatthews
