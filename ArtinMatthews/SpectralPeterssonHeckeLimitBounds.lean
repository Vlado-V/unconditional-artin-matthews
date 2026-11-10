module

public import ArtinMatthews.SpectralPeterssonHeckeSeed
public import ArtinMatthews.SpectralPeterssonHeckeGlobalBound
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

/-! The global weight-two bound passes to the pointwise Hecke limit
and to its actual cusp slashes. -/

noncomputable section
open Filter Set Matrix UpperHalfPlane
open scoped MatrixGroups Topology

namespace ArtinMatthews

theorem gamma0PeterssonHecke_limit_weighted_bound (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (n : ℕ+) (P : UpperHalfPlane → ℂ) (C : ℝ)
    (hbd : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane,
      ‖gamma0PeterssonHecke N a u n z‖*z.im ≤ C)
    (hlim : ∀ z : UpperHalfPlane,
      Tendsto (fun u : ℝ => gamma0PeterssonHecke N a u n z) (𝓝[>] 0) (𝓝 (P z))) :
    ∀ z : UpperHalfPlane, ‖P z‖*z.im ≤ C := by
  intro z
  have hnear : ∀ᶠ u : ℝ in 𝓝[>] 0, u ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
  exact le_of_tendsto ((hlim z).norm.mul_const z.im) (hnear.mono fun u hu => hbd u hu z)

theorem spectralPeterssonTwo_slash_weighted_bound (g : SL(2, ℝ)) (F : UpperHalfPlane → ℂ)
    {C : ℝ} (hbd : ∀ z : UpperHalfPlane, ‖F z‖*z.im ≤ C) (z : UpperHalfPlane) :
    ‖spectralHolomorphicSlash 2 g F z‖*z.im ≤ C := by
  have he := spectralPeterssonWeightedNorm_slash 2 g F z
  simp only [spectralPeterssonWeightedNorm_two] at he
  exact he.trans_le (hbd (g • z))

end ArtinMatthews
