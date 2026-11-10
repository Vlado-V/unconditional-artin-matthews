module

public import ArtinMatthews.SpectralGamma0EllipticMassCompletion
public import ArtinMatthews.SpectralGamma0EllipticBand
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
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

/-! Identification of the completed native Sobolev value with the actual
completed automorphic strip restriction on every cutoff plateau. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

include hab

theorem gamma0EllipticMass_band (N : ℕ) [NeZero N] {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (f : Gamma0RegionL2 N) :
    spectralEllipticPlaneToBand (2*(N:ℝ)) c d
      (spectralEllipticNativeToPlane (gamma0EllipticMass φ ha hφ r L N f)) =
      L.compLpL 2 (volume.restrict (spectralEllipticBand (2*(N:ℝ)) c d))
        (spectralEllipticStripBand (2*(N:ℝ)) hY hc
          (gamma0CuspTwoCellCoordinateRestriction N r Y hY f)) := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq
      ((spectralEllipticPlaneToBand (2*(N:ℝ)) c d).continuous.comp
        (spectralEllipticNativeToPlane.continuous.comp
          (gamma0EllipticMass φ ha hφ r L N).continuous))
      ((L.compLpL 2 _).continuous.comp
        ((spectralEllipticStripBand (2*(N:ℝ)) hY hc).continuous.comp
          (gamma0CuspTwoCellCoordinateRestriction N r Y hY).continuous)))
  intro ψ
  apply Lp.ext
  have hnative := spectralEllipticCoordinates_symm_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (gamma0EllipticMass_seed_ae φ ha hab hφ r L N ψ)
  have hstrip := (Measure.absolutelyContinuous_of_le_smul
    (cuspStripMeasure_band_le (2*(N:ℝ)) (b := d) hY hc)).ae_eq
      (gamma0CuspTwoCellCoordinateRestriction_seed_ae N r Y hY ψ)
  filter_upwards [spectralEllipticPlaneToBand_ae (2*(N:ℝ)) c d _,
    ae_restrict_of_ae (spectralEllipticNativeToPlane_ae _),
    ae_restrict_of_ae hnative, L.coeFn_compLpL (p := 2) (μ := volume.restrict
      (spectralEllipticBand (2*(N:ℝ)) c d)) _,
    spectralEllipticStripBand_ae (2*(N:ℝ)) hY hc _, hstrip,
    ae_restrict_mem (spectralEllipticBand_measurable (2*(N:ℝ)) c d)]
    with p hp1 hp2 hp3 hp4 hp5 hp6 hp
  simp only [Function.comp_apply] at hp3 ⊢
  rw [hp1, hp2, hp3, hp4, hp5, hp6]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [hplateau p hp, one_mul]
  congr 1
  exact (spectralSectionSmoothExtension_eq hY (gamma0CuspSection N ψ r)
    (hc.le.trans hp.2.1)).symm

theorem gamma0EllipticMass_band_ae (N : ℕ) [NeZero N] {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (f : Gamma0RegionL2 N) :
    gamma0EllipticMass φ ha hφ r L N f =ᵐ[volume.restrict
      (spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d)]
      fun x => L (gamma0CuspTwoCellCoordinateRestriction N r Y hY f
        (spectralEllipticCoordinates x)) := by
  have he := gamma0EllipticMass_band φ ha hab hφ r L N hY hc hplateau f
  have hp : (fun p => gamma0EllipticMass φ ha hφ r L N f
      (spectralEllipticCoordinates.symm p)) =ᵐ[volume.restrict
        (spectralEllipticBand (2*(N:ℝ)) c d)]
      fun p => L (gamma0CuspTwoCellCoordinateRestriction N r Y hY f p) := by
    filter_upwards [spectralEllipticPlaneToBand_ae (2*(N:ℝ)) c d _,
      ae_restrict_of_ae (spectralEllipticNativeToPlane_ae _),
      L.coeFn_compLpL (p := 2) (μ := volume.restrict
        (spectralEllipticBand (2*(N:ℝ)) c d)) _,
      spectralEllipticStripBand_ae (2*(N:ℝ)) hY hc _] with p hp1 hp2 hp3 hp4
    have hh := congrArg (fun v : Lp ℝ 2 (volume.restrict
      (spectralEllipticBand (2*(N:ℝ)) c d)) => v p) he
    rw [hp1, hp2, hp3, hp4] at hh
    exact hh
  have hmp := spectralEllipticCoordinates_measurePreserving.restrict_preimage
    (spectralEllipticBand_measurable (2*(N:ℝ)) c d)
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using
    hmp.quasiMeasurePreserving.ae_eq_comp hp

theorem gamma0EllipticPair_band (N : ℕ) [NeZero N] {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (u : gamma0EnergySpace N) :
    spectralEllipticPlaneToBand (2*(N:ℝ)) c d
      (spectralEllipticNativeToPlane (gamma0EllipticPair φ ha hφ r L N u).1) =
      L.compLpL 2 (volume.restrict (spectralEllipticBand (2*(N:ℝ)) c d))
        (spectralEllipticStripBand (2*(N:ℝ)) hY hc
          (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N u))) := by
  rw [← gamma0EllipticMass_energy φ ha hab hφ r L N u]
  exact gamma0EllipticMass_band φ ha hab hφ r L N hY hc hplateau _

end ArtinMatthews
