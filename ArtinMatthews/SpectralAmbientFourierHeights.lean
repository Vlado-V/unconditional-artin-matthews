module

public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralGamma0FourierEnergy
public import ArtinMatthews.SpectralCuspWeightedGluingRepresentative
public import ArtinMatthews.SpectralModularDensity
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

/-! Actual nonzero and zero Fourier projections agree on nested cusp heights. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology

namespace ArtinMatthews

theorem gamma0CuspFourierCoefficient_height_restriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂)
    (n : ℤ) (f : Gamma0RegionL2 N) :
    cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h (gamma0CuspFourierCoefficient N r Y₁ hY₁ n f) =
      gamma0CuspFourierCoefficient N r Y₂ hY₂ n f := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq ((cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h).continuous.comp
      (gamma0CuspFourierCoefficient N r Y₁ hY₁ n).continuous)
      (gamma0CuspFourierCoefficient N r Y₂ hY₂ n).continuous)
  intro ψ
  change cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h
      (gamma0CuspFourierCoefficient N r Y₁ hY₁ n (gamma0SmoothSeedMass N ψ)) =
    gamma0CuspFourierCoefficient N r Y₂ hY₂ n (gamma0SmoothSeedMass N ψ)
  apply Lp.ext
  have hc₁ := Measure.ae_smul_measure (gamma0CuspFourierCoefficient_seed_ae N ψ r Y₁ hY₁ n)
    (cuspHorizontalMeasure (N : ℝ) univ)
  have hc₁' := (Measure.absolutelyContinuous_of_le
    (cuspWeightedVerticalMeasure_mono (N : ℝ) h)).ae_eq hc₁
  have hc₂ := Measure.ae_smul_measure (gamma0CuspFourierCoefficient_seed_ae N ψ r Y₂ hY₂ n)
    (cuspHorizontalMeasure (N : ℝ) univ)
  filter_upwards [cuspVerticalLpRestriction_ae (N : ℝ) Y₁ Y₂ h
    (gamma0CuspFourierCoefficient N r Y₁ hY₁ n (gamma0SmoothSeedMass N ψ)), hc₁', hc₂,
    cuspWeightedVerticalMeasure_ae_gt (N : ℝ) Y₂ hY₂] with y hr hc₁ hc₂ hy
  rw [hr, hc₁, hc₂]
  have he : (fun x : ℝ => gamma0CuspSeedPlaneExtension N ψ r Y₁ (x, y)) =
      (fun x : ℝ => gamma0CuspSeedPlaneExtension N ψ r Y₂ (x, y)) := by
    funext x
    change spectralSectionSmoothExtension Y₁ (gamma0CuspSection N ψ r) (x, y) =
      spectralSectionSmoothExtension Y₂ (gamma0CuspSection N ψ r) (x, y)
    rw [spectralSectionSmoothExtension_eq hY₁ _ (h.trans hy.le),
      spectralSectionSmoothExtension_eq hY₂ _ hy.le]
  unfold cuspHorizontalWeightedMean cuspHorizontalMean
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  change cuspFourierPhase (N : ℝ) n x * gamma0CuspSeedPlaneExtension N ψ r Y₁ (x, y) =
    cuspFourierPhase (N : ℝ) n x * gamma0CuspSeedPlaneExtension N ψ r Y₂ (x, y)
  rw [congrFun he x]

theorem gamma0CuspFourierCoefficient_height_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂)
    (n : ℤ) (f : Gamma0RegionL2 N) :
    gamma0CuspFourierCoefficient N r Y₁ hY₁ n f =ᵐ[volume.restrict (Ioi Y₂)]
      gamma0CuspFourierCoefficient N r Y₂ hY₂ n f := by
  have hr := cuspVerticalLpRestriction_ae (N : ℝ) Y₁ Y₂ h
    (gamma0CuspFourierCoefficient N r Y₁ hY₁ n f)
  rw [gamma0CuspFourierCoefficient_height_restriction N r Y₁ Y₂ hY₁ hY₂ h n f] at hr
  exact (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY₂).mp hr.symm

end ArtinMatthews
