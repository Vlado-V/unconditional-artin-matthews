module

public import ArtinMatthews.SpectralGamma0LocalizationCompact
public import ArtinMatthews.SpectralCuspGraphRestriction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Compact localizations in the actual finite modular-chart mass space. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem h2_integer_measurePreserving (r : SL(2, ℤ)) :
    MeasurePreserving (fun z : UpperHalfPlane => r • z) volume volume := by
  change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z) _ _
  exact measurePreserving_smul _ _

def h2ModularChartLp (r : SL(2, ℤ)) :
    Lp ℂ 2 (volume : Measure UpperHalfPlane) →L[ℝ] Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (spectralLpMeasureRestriction Measure.restrict_le_self).comp
    ((Lp.compMeasurePreservingₗᵢ ℂ (fun z : UpperHalfPlane => r⁻¹ • z)
      (h2_integer_measurePreserving r⁻¹)).toContinuousLinearMap.restrictScalars ℝ)

theorem h2ModularChartLp_ae (r : SL(2, ℤ)) (f : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    h2ModularChartLp r f =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => f (r⁻¹ • z)) := by
  have hc := Lp.coeFn_compMeasurePreserving f (h2_integer_measurePreserving r⁻¹)
  have hr := spectralLpMeasureRestriction_ae (μ := (volume : Measure UpperHalfPlane))
    (ν := volume.restrict ModularGroup.fd) Measure.restrict_le_self
    (Lp.compMeasurePreservingₗᵢ ℂ (fun z : UpperHalfPlane => r⁻¹ • z)
      (h2_integer_measurePreserving r⁻¹) f)
  exact hr.trans ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq hc)

/-- Actual finite-coset chart restriction of an ambient invariant-volume L² function. -/
def gamma0GlobalChartsLp (N : ℕ) [NeZero N] :
    Lp ℂ 2 (volume : Measure UpperHalfPlane) →L[ℝ] Gamma0RegionL2 N :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      Lp ℂ 2 (volume.restrict ModularGroup.fd))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N => h2ModularChartLp q.out))

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

def gamma0CompactMassMap (N : ℕ) [NeZero N] :
    gamma0EnergySpace N →L[ℝ] Gamma0RegionL2 N :=
  (gamma0GlobalChartsLp N).comp ((gamma0EnergyLocalization φ ha hab hφ N).restrictScalars ℝ)

theorem gamma0CompactMassMap_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0CompactMassMap φ ha hab hφ N) :=
  (gamma0EnergyLocalization_compact φ ha hab hφ N).clm_comp (gamma0GlobalChartsLp N)

theorem gamma0CompactMassMap_seed_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd] (fun z =>
        φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)*gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)) := by
  change (h2ModularChartLp q.out (gamma0EnergyLocalization φ ha hab hφ N (gamma0EnergyTest N ψ)) :
    UpperHalfPlane → ℂ) =ᵐ[volume.restrict ModularGroup.fd] _
  rw [gamma0EnergyLocalization_apply]
  apply (h2ModularChartLp_ae q.out _).trans
  have hcomp := (h2_integer_measurePreserving q.out⁻¹).quasiMeasurePreserving.ae_eq_comp
    (gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ)
  exact (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self : (volume : Measure UpperHalfPlane).restrict ModularGroup.fd ≤ volume)).ae_eq hcomp

/-- The compact approximant has exactly the literal localized finite-chart mass. -/
theorem gamma0CompactMassMap_seed_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ)‖^2 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd,
          ‖φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)*gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro q _
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0CompactMassMap_seed_ae φ ha hab hφ N ψ q] with z hz
  rw [real_inner_self_eq_norm_sq]
  change ‖(gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q) z‖^2 = _
  rw [hz]

end ArtinMatthews
