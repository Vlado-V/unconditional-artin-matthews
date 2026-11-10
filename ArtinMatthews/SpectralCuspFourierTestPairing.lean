module

public import ArtinMatthews.SpectralCuspFourierTestSeed
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralGamma0FourierEnergy
public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralCuspCompletedUnfolding
public import ArtinMatthews.SpectralCuspSeparableCoordinates
public import ArtinMatthews.SpectralCuspSeparablePairingFixedHeight
public import ArtinMatthews.SpectralCuspTwoCellFourier
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

/-! Literal Fourier testing of completed cusp restrictions.  The two-cell
partition reduces to one period; the raw arithmetic Poincare lift still
contains the actual central-sign factor two. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal ContDiff MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem cuspTwoCellExtension_fourier_ae {w : ℝ} (hw : 0 < w) (Y : ℝ) (n : ℤ)
    (f : CuspStripL2 w Y) :
    cuspTwoCellExtension hw.le Y (cuspFourierMultiplier w Y w n f)
      =ᵐ[cuspStripMeasure (2 * w) Y]
      fun p => cuspFourierPhase w n p.1 * cuspTwoCellExtension hw.le Y f p := by
  have hmul := Measure.ae_smul_measure (cuspFourierMultiplyLp_ae w Y w n f) (2 : ℝ≥0∞)
  have hfold := (spectralTwoCellCoordinateFold_preserving hw.le Y).quasiMeasurePreserving.ae_eq_comp hmul
  filter_upwards [cuspTwoCellExtension_ae hw.le Y (cuspFourierMultiplier w Y w n f),
    cuspTwoCellExtension_ae hw.le Y f, hfold] with p hp hq hr
  rw [hp, hq]
  change cuspFourierMultiplyLp w Y w n f (spectralTwoCellCoordinateFold w p) = _
  simpa only [Function.comp_def, spectralTwoCellCoordinateFold,
    cuspFourierPhase_fold w hw n] using hr

theorem cuspTwoCell_fourier_partition_pairing {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (n : ℤ) (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ, (spectralHorizontalPartition w p.1 * ρ p.2) •
      (cuspFourierPhase w n p.1 * cuspTwoCellExtension hw.le Y f p)
        ∂cuspStripMeasure (2 * w) Y) =
      w • ∫ y in Ioi Y, (ρ y / y ^ 2) • (cuspFourierProjection w Y w n f) y := by
  calc
    _ = ∫ p : ℝ × ℝ, (spectralHorizontalPartition w p.1 * ρ p.2) •
        cuspTwoCellExtension hw.le Y (cuspFourierMultiplier w Y w n f) p
          ∂cuspStripMeasure (2 * w) Y := by
      apply integral_congr_ae
      filter_upwards [cuspTwoCellExtension_fourier_ae hw Y n f] with p hp
      rw [hp]
    _ = _ := cuspTwoCell_partition_pairing hw hY ρ hρ hcρ _

theorem gamma0CuspFourierTest_pairing (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ ((cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        n ρ hρ hcρ hpos).val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z)) =
      (N : ℝ) • ∫ y in Ioi Y, (ρ y / y ^ 2) •
        (gamma0CuspFourierCoefficient N r Y hY n f) y := by
  let f₀ : CuspStripL2 (N : ℝ) Y :=
    (cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspMassRestriction N r Y hY f)
  change (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
    inner ℂ ((cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      n ρ hρ hcρ hpos).val z)
      (cuspHyperbolicPullback (2 * (N : ℝ)) Y hY
        (cuspTwoCellExtension (Nat.cast_nonneg N) Y f₀) z)) = _
  simp_rw [cuspFourierTestSeed_apply]
  rw [cuspHyperbolicPullback_pairing_coordinates (2 * (N : ℝ)) Y hY
    (fun p => ((spectralHorizontalPartition (N : ℝ) p.1 * ρ p.2 : ℝ) : ℂ) *
      star (cuspFourierPhase (N : ℝ) n p.1))]
  have hi (p : ℝ × ℝ) :
      inner ℂ (((spectralHorizontalPartition (N : ℝ) p.1 * ρ p.2 : ℝ) : ℂ) *
        star (cuspFourierPhase (N : ℝ) n p.1))
        (cuspTwoCellExtension (Nat.cast_nonneg N) Y f₀ p) =
      (spectralHorizontalPartition (N : ℝ) p.1 * ρ p.2) •
        (cuspFourierPhase (N : ℝ) n p.1 *
          cuspTwoCellExtension (Nat.cast_nonneg N) Y f₀ p) := by
    have hr (s : ℝ) : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
    simp only [RCLike.inner_apply, map_mul, starRingEnd_apply, star_star, hr,
      Complex.real_smul]
    ring
  simp_rw [hi]
  exact cuspTwoCell_fourier_partition_pairing (Nat.cast_pos.mpr (NeZero.pos N))
    hY n ρ hρ.continuous hcρ f₀

def gamma0FourierPoincareTest (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) : Gamma0RegionL2 N :=
  gamma0SmoothSeedMass N (modularTranslateSmoothSeed r
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpos))

theorem gamma0FourierPoincareTest_inner (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y)
    (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos) f =
      (2 * (N : ℝ)) • ∫ y in Ioi Y, (ρ y / y ^ 2) •
        (gamma0CuspFourierCoefficient N r Y hY n f) y := by
  rw [gamma0FourierPoincareTest, gamma0Mass_inner_unfold_twoCell_integral N r Y hY _
    (cuspFourierTestSeed_support _ _ _ _ _ _ _ Y hs) f,
    gamma0CuspFourierTest_pairing N r Y hY n ρ hρ hcρ hpos f]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

end ArtinMatthews
