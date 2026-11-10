module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralCuspVerticalTesting
public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative
public import ArtinMatthews.SpectralCuspPositiveTestWeights
public import ArtinMatthews.SpectralCuspWeakRegularityLocal
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

/-! Exact compact testing of the actual globally glued constant terms,
through their bounded genuine positive-height operators. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0GlobalCuspConstantTerm_compact_test (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ Ioi Y) :
    (∫ y in Ioi (0 : ℝ), κ y • gamma0GlobalCuspConstantTerm N r f y) =
      cuspVerticalCompactTest (Nat.cast_pos.mpr (NeZero.pos N)) hY κ hκ hκc
        (gamma0CuspConstantTerm N r Y hY f) := by
  rw [cuspVerticalCompactTest_apply,
    spectralTest_setIntegral_eq_integral κ (Ioi (0 : ℝ))
      (fun _ hy => hY.trans (hκs hy)),
    ← spectralTest_setIntegral_eq_integral κ (Ioi Y) hκs]
  have he := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTerm_ae N r f Y hY)
  apply integral_congr_ae
  exact he.mono fun y hy => by dsimp only; rw [hy]

theorem gamma0GlobalCuspConstantTerm_test_integrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun y => κ y • gamma0GlobalCuspConstantTerm N r f y) volume :=
  SpectralCuspWeakRegularity.integrable_positive_test_smul
    (gamma0GlobalCuspConstantTerm_locallyIntegrable N r f) hκ hκc hκs

theorem gamma0GlobalCuspConstantTermDerivative_compact_test (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) (Y : ℝ) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hκc : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ Ioi Y) :
    (∫ y in Ioi (0 : ℝ), κ y • gamma0GlobalCuspConstantTermDerivative N r u y) =
      cuspVerticalCompactTest (Nat.cast_pos.mpr (NeZero.pos N)) hY
        (fun y => κ y / y)
        (by simpa only [pow_one] using
          (spectralPositiveTest_div_pow_contDiff κ hκ
            (fun _ hy => hY.trans (hκs hy)) 1).continuous)
        (by simpa only [pow_one] using spectralPositiveTest_div_pow_compact κ hκc 1)
        (gamma0CuspVerticalConstantTerm N r Y hY u) := by
  rw [cuspVerticalCompactTest_apply,
    spectralTest_setIntegral_eq_integral κ (Ioi (0 : ℝ))
      (fun _ hy => hY.trans (hκs hy)),
    ← spectralTest_setIntegral_eq_integral κ (Ioi Y) hκs]
  have he := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTermDerivative_ae N r u Y hY)
  apply integral_congr_ae
  filter_upwards [he] with y hy
  rw [hy]
  simp only [gamma0CuspConstantTermDerivative, div_eq_mul_inv, mul_smul]

end ArtinMatthews
