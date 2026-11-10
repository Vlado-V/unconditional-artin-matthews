module

public import ArtinMatthews.SpectralEisensteinFourierBesselInitial
public import ArtinMatthews.SpectralPrimitiveEisensteinTrace
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual compact primitive Eisenstein test is the initial arithmetic
amplitude times the genuine K transform of the width-dilated profile. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0PrimitiveEisensteinTransform_initial_bessel (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (s : ℂ) (hs : 1 < s.re) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0PrimitiveEisensteinTransform N a r Y hY n s ρ =
      gamma0CuspInitialFourierAmplitude N r a n s*
        cuspBesselTransform (s-1/2) (2*Real.pi*|(n : ℝ)|)
          (Y/(gamma0CuspTrueWidth N r : ℝ))
          (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by
  rw [gamma0PrimitiveEisensteinTransform_initial N a r Y hY n s hs ρ hρ hcρ hpρ hsρ]
  unfold cuspBesselTransform
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have hu0 : 0 < u := (div_pos hY (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))).trans hu
  rw [gamma0UnitCuspFourierMean_initial_bessel N r a s hs n hn u hu0]
  simp only [cuspBesselTransformIntegrand,Complex.real_smul]
  ring

theorem gamma0PrimitiveEisensteinTest_initial_bessel (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (s : ℂ) (hs : 1 < s.re) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0CuspEisensteinMeromorphicTest N a
      (gamma0PrimitiveFourierPoincareSeed N r n ρ hρ hcρ hpρ) s =
      gamma0CuspInitialFourierAmplitude N r a n s*
        cuspBesselTransform (s-1/2) (2*Real.pi*|(n : ℝ)|)
          (Y/(gamma0CuspTrueWidth N r : ℝ))
          (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by
  rw [← gamma0PrimitiveEisensteinTransform_eq_test N a r Y hY n s ρ hρ hcρ hpρ hsρ]
  exact gamma0PrimitiveEisensteinTransform_initial_bessel N a r Y hY n hn s hs ρ hρ hcρ hpρ hsρ

theorem gamma0PrimitiveEisensteinTransform_meromorphic (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    Meromorphic (fun s => gamma0PrimitiveEisensteinTransform N a r Y hY n s ρ) := by
  have h : (fun s => gamma0PrimitiveEisensteinTransform N a r Y hY n s ρ) =
      gamma0CuspEisensteinMeromorphicTest N a
        (gamma0PrimitiveFourierPoincareSeed N r n ρ hρ hcρ hpρ) := by
    funext s
    exact gamma0PrimitiveEisensteinTransform_eq_test N a r Y hY n s ρ hρ hcρ hpρ hsρ
  rw [h]
  exact gamma0CuspEisensteinMeromorphicTest_meromorphic N a _

end ArtinMatthews
