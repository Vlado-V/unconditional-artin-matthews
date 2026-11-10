module

public import ArtinMatthews.SpectralCuspSeparableSupport
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralCuspSeparableCoordinates
public import ArtinMatthews.SpectralCuspSeparablePairingFixedHeight
public import ArtinMatthews.SpectralCuspSeparablePairingProduct
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

/-! Exact real compact-test and positive-Laplacian evaluations against the
actual completed two-cell mass restriction. The right side uses its genuine
bounded constant-term operator. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff MatrixGroups InnerProductSpace

 theorem gamma0CuspTwoCellMassRestriction_test_pairing (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ ((cuspConstantTermTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ρ hρ hρc hρpos).val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z)) =
      (N : ℝ) • ∫ y in Ioi Y, (ρ y / y ^ 2) • (gamma0CuspConstantTerm N r Y hY f) y := by
  simp only [cuspConstantTermTestSeed, h2RealSeparableSmoothSeed_apply]
  rw [gamma0CuspTwoCellMassRestriction_separable_pairing]
  exact cuspTwoCell_partition_pairing (Nat.cast_pos.mpr (NeZero.pos N)) hY
    ρ hρ.continuous hρc
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspMassRestriction N r Y hY f))

 theorem gamma0CuspTwoCellMassRestriction_laplacian_pairing (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ ((h2SectionLaplacianSeed (cuspConstantTermTestSeed (N : ℝ)
        (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hρpos)).val z)
        (gamma0CuspTwoCellMassRestriction N r Y hY f z)) =
      -((N : ℝ) • ∫ y in Ioi Y, deriv (deriv ρ) y •
        (gamma0CuspConstantTerm N r Y hY f) y) := by
  let f₀ : CuspStripL2 (N : ℝ) Y :=
    (cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspMassRestriction N r Y hY f)
  let ψ := cuspConstantTermTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hρpos
  let t : ℝ × ℝ → ℂ := fun p =>
    ((-(p.2 ^ 2) * (deriv (deriv (spectralHorizontalPartition (N : ℝ))) p.1 * ρ p.2 +
      spectralHorizontalPartition (N : ℝ) p.1 * deriv (deriv ρ) p.2) : ℝ) : ℂ)
  have ht (z : UpperHalfPlane) : (h2SectionLaplacianSeed ψ).val z = t (z.re, z.im) := by
    rw [h2SectionLaplacianSeed_apply]
    exact h2RealSeparableSmoothSeed_laplacian _ _ _ _ _ _ _ z
  change (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
    inner ℂ ((h2SectionLaplacianSeed ψ).val z)
      (cuspHyperbolicPullback (2 * (N : ℝ)) Y hY
        (cuspTwoCellExtension (Nat.cast_nonneg N) Y f₀) z)) = _
  simp_rw [ht]
  rw [cuspHyperbolicPullback_pairing_coordinates]
  have hi (p : ℝ × ℝ) : inner ℂ (t p) (cuspTwoCellExtension (Nat.cast_nonneg N) Y f₀ p) =
      (-(p.2 ^ 2) * (deriv (deriv (spectralHorizontalPartition (N : ℝ))) p.1 * ρ p.2 +
        spectralHorizontalPartition (N : ℝ) p.1 * deriv (deriv ρ) p.2)) •
        cuspTwoCellExtension (Nat.cast_nonneg N) Y f₀ p := by
    simp only [t, RCLike.inner_apply, Complex.real_smul, Complex.conj_ofReal]
    exact mul_comm _ _
  simp_rw [hi]
  exact cuspTwoCell_partition_laplacian_pairing (Nat.cast_pos.mpr (NeZero.pos N)) hY ρ hρ hρc f₀

end
end ArtinMatthews
