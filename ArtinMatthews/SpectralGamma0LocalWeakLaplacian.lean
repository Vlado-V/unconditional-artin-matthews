module

public import ArtinMatthews.SpectralGamma0WeakInverse
public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralSectionLaplacian
public import ArtinMatthews.SpectralGamma0LocalDifferentialForm
public import ArtinMatthews.SpectralModularDensityCharts
public import ArtinMatthews.SpectralSectionModularTests
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Green vector solves the literal coordinate equation
(1 - y²(∂x²+∂y²))u=f against every compact smooth interior chart test.
This is a consequence of the genuine energy construction, not a PDE premise. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0InteriorChartSeed_mass_pairing (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (ψ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0EnergyInclusion N (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ))) f =
      ∫ z in ModularGroup.fd, inner ℂ (ψ.val z) ((f q) z) := by
  classical
  rw [gamma0EnergyInclusion_test,modularInteriorChartSeed_mass_single N q ψ hψ
    (modularSectionLp ψ) (modularSectionLp_ae ψ),PiLp.inner_apply]
  rw [Finset.sum_eq_single q]
  · rw [PiLp.single_eq_same,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [modularSectionLp_ae ψ] with z hz
    rw [hz]
  · intro t _ ht
    rw [PiLp.single_eq_of_ne 2 ht,inner_zero_left]
  · simp

theorem gamma0Green_local_weak_laplacian (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (ψ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (f : Gamma0RegionL2 N) :
    (∫ z in ModularGroup.fd, inner ℂ (ψ.val z) (((gamma0Green N f) q) z)) +
      (∫ z in ModularGroup.fd, inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        (((gamma0Green N f) q) z)) =
      ∫ z in ModularGroup.fd, inner ℂ (ψ.val z) ((f q) z) := by
  have hg : gamma0EnergyMassChart N q (gamma0WeakSolution N f) = (gamma0Green N f) q := by
    rw [gamma0Green_apply]
    rfl
  have hlocal := gamma0Energy_completed_local_differential_pairing N q ψ hψ (gamma0WeakSolution N f)
  rw [hg] at hlocal
  rw [← hlocal]
  calc
    _ = star (inner ℂ (gamma0WeakSolution N f)
      (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ))) := by
        simpa only [starRingEnd_apply] using
          (inner_conj_symm (𝕜 := ℂ) (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ))
            (gamma0WeakSolution N f)).symm
    _ = star (inner ℂ f (gamma0EnergyInclusion N
      (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ)))) := by
        rw [gamma0WeakSolution_equation]
    _ = _ := by
      have hc : star (inner ℂ f (gamma0EnergyInclusion N
          (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ)))) =
          inner ℂ (gamma0EnergyInclusion N
            (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ))) f := by
        simpa only [starRingEnd_apply] using
          (inner_conj_symm (𝕜 := ℂ) (gamma0EnergyInclusion N
            (gamma0EnergyTest N (modularInteriorChartSeed q.out ψ))) f)
      exact hc.trans (gamma0InteriorChartSeed_mass_pairing N q ψ hψ f)

end ArtinMatthews
