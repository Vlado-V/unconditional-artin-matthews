module

public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralCuspEisensteinAutomorphy
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

/-! Actual automorphy of the cutoff, remainder and compact forcing. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspHeightProfile_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (f : ℝ → ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspHeightProfile N a f (g.val • z)=gamma0CuspHeightProfile N a f z := by
  unfold gamma0CuspHeightProfile
  congr 1
  have h := finsum_comp_equiv
    (f := fun v : Gamma0CuspEisensteinRows N 1 a =>
      f (cuspEisensteinRowHeight N 1 a v z/(gamma0CuspTrueWidth N a:ℝ)))
    (cuspEisensteinAutomorphyEquiv N a g)
  simpa only [cuspEisensteinRowHeight_automorphy] using h

theorem gamma0CuspEisensteinCutoff_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCutoff N a s (g.val • z)=gamma0CuspEisensteinCutoff N a s z := by
  rw [gamma0CuspEisensteinCutoff_eq_profile,gamma0CuspEisensteinCutoff_eq_profile]
  exact gamma0CuspHeightProfile_automorphy N a _ g z

theorem gamma0CuspEisensteinRemainder_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisensteinRemainder N a s (g.val • z)=gamma0CuspEisensteinRemainder N a s z := by
  rw [gamma0CuspEisensteinRemainder,gamma0CuspEisensteinRemainder,
    gamma0CuspEisenstein_automorphy,gamma0CuspEisensteinCutoff_automorphy]

theorem gamma0CuspEisensteinCompactForcing_automorphy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCompactForcing N a s (g.val • z)=gamma0CuspEisensteinCompactForcing N a s z :=
  gamma0CuspHeightProfile_automorphy N a _ g z

theorem gamma0CuspEisensteinCompactForcing_continuous (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) : Continuous (gamma0CuspEisensteinCompactForcing N a s) := by
  have he : gamma0CuspEisensteinCompactForcing N a s=
      (1/2:ℂ) • gamma0PoincareSeed N
        (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
          (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
          (eisensteinVerticalCutoffError_positive_support s)).val :=
    funext (gamma0CuspEisensteinCompactForcing_eq_poincare N a s)
  rw [he]
  exact continuous_const.smul (gamma0PoincareSeed N _).continuous

end ArtinMatthews
