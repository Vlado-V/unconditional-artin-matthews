module

public import ArtinMatthews.SpectralCuspGlobalOutgoingEigenmode
public import ArtinMatthews.SpectralGamma0CosetCharts


set_option backward.privateInPublic true
@[expose] public section

/-! Every completed constant term equals the term in the corresponding
finite congruence chart. No new cusp injectivity assumption is used. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspMassRestriction_eq_finiteChart (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (f : Gamma0RegionL2 N) :
    gamma0CuspMassRestriction N r Y hY f=
      gamma0CuspMassRestriction N (QuotientGroup.mk r : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out Y hY f := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq (by fun_prop) (by fun_prop))
  intro ψ
  apply Lp.ext
  let q := (QuotientGroup.mk r : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  filter_upwards [gamma0CuspMassRestriction_seed_ae N r Y hY ψ,
    gamma0CuspMassRestriction_seed_ae N q.out Y hY ψ] with z hr hq
  rw [hr,hq]
  exact gamma0_inverse_chart_representative N (gamma0PoincareSeed N ψ.val)
    (gamma0PoincareSeed_invariant N ψ.val) r z

theorem gamma0GlobalCuspConstantTerm_eq_finiteChart (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (f : Gamma0RegionL2 N) :
    gamma0GlobalCuspConstantTerm N r f=ᵐ[volume.restrict (Ioi 0)]
      gamma0GlobalCuspConstantTerm N (QuotientGroup.mk r : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out f := by
  let q := (QuotientGroup.mk r : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  apply spectralCuspWeightedGluing_unique (w:=(N:ℝ)) (Nat.cast_pos.mpr (NeZero.pos N))
  intro n
  let Y := spectralCuspGluingHeight n
  have hY : 0<Y := spectralCuspGluingHeight_pos n
  have he : gamma0CuspConstantTerm N r Y hY f=gamma0CuspConstantTerm N q.out Y hY f := by
    change cuspHyperbolicConstantTerm (N:ℝ) Y hY (gamma0CuspMassRestriction N r Y hY f)=_
    rw [gamma0CuspMassRestriction_eq_finiteChart N r Y hY f]
    rfl
  filter_upwards [gamma0GlobalCuspConstantTerm_ae N r f Y hY,
    gamma0GlobalCuspConstantTerm_ae N q.out f Y hY] with y hr hq
  rw [hr,hq,he]

theorem gamma0Mass_cuspidal_of_finiteChart_means_zero (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N)
    (hf : ∀ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      gamma0GlobalCuspConstantTerm N q.out f=ᵐ[volume.restrict (Ioi 0)] 0) :
    f∈gamma0AllHeightCuspidalMassSpace N := by
  rw [mem_gamma0AllHeightCuspidalMassSpace_iff_globalConstantTerm]
  intro r
  exact (gamma0GlobalCuspConstantTerm_eq_finiteChart N r f).trans (hf _)

end ArtinMatthews
