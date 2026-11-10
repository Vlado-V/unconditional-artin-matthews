module

public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralModularBoundary
public import ArtinMatthews.SpectralModularDensityPeriodization
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth periodizations realize independent compact smooth data in
each finite modular chart.  These identities concern literal `Lp` classes in
the full chart product, before any completion or cusp restriction. -/

noncomputable section
open Set MeasureTheory
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

attribute [local instance] Classical.propDecidable

theorem modular_fdo_ae_on_fd :
    ∀ᵐ z : UpperHalfPlane ∂volume.restrict ModularGroup.fd, z ∈ ModularGroup.fdo := by
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet,
    ae_restrict_of_ae modular_fd_ae_eq_fdo] with z hz he
  exact he.mp hz

/-- Every actual smooth compact interior datum is realized in exactly one
finite-coset chart by a normalized genuine smooth periodization. -/
theorem modularInteriorChartSeed_mass_single (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (f : Lp ℂ 2 (volume.restrict ModularGroup.fd))
    (hf : f =ᵐ[volume.restrict ModularGroup.fd] ψ.val) :
    gamma0SmoothSeedMass N (modularInteriorChartSeed q.out ψ) = PiLp.single 2 q f := by
  classical
  apply PiLp.ext
  intro t
  by_cases ht : t = q
  · subst t
    rw [PiLp.single_eq_same]
    apply Lp.ext
    filter_upwards [gamma0SeedMass_coeFn N (modularInteriorChartSeed q.out ψ).val q,
      hf, modular_fdo_ae_on_fd] with z hmass hfeq hz
    change (gamma0SeedMass N (modularInteriorChartSeed q.out ψ).val q) z = f z
    rw [hmass, modularInteriorChartSeed_periodization_self N q.out ψ hψ hz, hfeq]
  · rw [PiLp.single_eq_of_ne 2 ht]
    apply Lp.ext
    filter_upwards [gamma0SeedMass_coeFn N (modularInteriorChartSeed q.out ψ).val t,
      modular_fdo_ae_on_fd, Lp.coeFn_zero ℂ 2 (volume.restrict ModularGroup.fd)]
      with z hmass hz hzero
    change (gamma0SeedMass N (modularInteriorChartSeed q.out ψ).val t) z =
      (0 : Lp ℂ 2 (volume.restrict ModularGroup.fd)) z
    rw [hmass, hzero]
    apply gamma0PoincareSeed_eq_zero_of_interior_chart_ne N _ q.out t.out
      (modularInteriorChartSeed_support q.out ψ hψ) _ hz
    simpa only [Quotient.out_eq'] using Ne.symm ht

/-- The actual mass core contains every single-coordinate smooth interior
datum; the support and normalization are discharged by the preceding seed. -/
theorem gamma0CompactCoreL2_contains_single_smooth_interior (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (f : Lp ℂ 2 (volume.restrict ModularGroup.fd))
    (hf : f =ᵐ[volume.restrict ModularGroup.fd] ψ.val) :
    PiLp.single 2 q f ∈ gamma0CompactCoreL2 N := by
  rw [← modularInteriorChartSeed_mass_single N q ψ hψ f hf]
  exact gamma0SmoothSeedMass_mem_core N _

end ArtinMatthews
