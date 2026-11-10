module

public import ArtinMatthews.SpectralABLResidualExceptionalMoment
public import ArtinMatthews.SpectralABLExceptionalDiagonalWeil
public import ArtinMatthews.SpectralInfinityResidualGap
public import ArtinMatthews.SpectralMixedCuspResidualGap
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

/-! The actual finite residual moment satisfies the same source exceptional
Weil scale at infinity and the mixed cusp. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0ABLExceptional_mixed_residual_density_le (A : ℕ) (hA : 3 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (n : ℤ) (hn : n ≠ 0) (a : ℝ), 0 < a → a ≤ 1 →
      let N := r*s
      c*Real.cos (Real.pi/4)*gamma0ResidualCosineExceptionalMoment N (gamma0CuspOneOver s) n hn a ≤
        (spectralABLExceptionalBound A/Real.pi+
          D*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
            (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)))/4 := by
  obtain ⟨c,hc,hLower⟩ := gamma0ABLExceptional_residual_cosine_weighted_le A hA
  obtain ⟨D,hD,hUpper⟩ := gamma0ABLExceptional_mixed_bare_diagonal_bound A hA hε
  refine ⟨c,D,hc,hD,?_⟩
  intro r s ir is hcop n hn a ha ha1
  have h := hLower (r*s) (gamma0CuspOneOver s) n hn 1 one_pos a ha
    (fun l j hρ => gamma0MixedCusp_residual_value_ge_three_sixteenths_of_rho r s hcop l j n hn hρ)
  exact h.trans ((Complex.re_le_norm _).trans (hUpper r s hcop 1 one_pos n hn a ha ha1))

theorem gamma0ABLExceptional_infinity_residual_density_le (A : ℕ) (hA : 3 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ (N : ℕ) [NeZero N],
      ∀ (n : ℤ) (hn : n ≠ 0) (a : ℝ), 0 < a → a ≤ 1 →
      c*Real.cos (Real.pi/4)*gamma0ResidualCosineExceptionalMoment N 1 n hn a ≤
        (spectralABLExceptionalBound A/Real.pi+
          D*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
            (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)))/4 := by
  obtain ⟨c,hc,hLower⟩ := gamma0ABLExceptional_residual_cosine_weighted_le A hA
  obtain ⟨D,hD,hUpper⟩ := gamma0ABLExceptional_infinity_bare_diagonal_bound A hA hε
  refine ⟨c,D,hc,hD,?_⟩
  intro N inst n hn a ha ha1
  have h := hLower N 1 n hn 1 one_pos a ha
    (fun l j hρ => gamma0Infinity_residual_value_ge_three_sixteenths_of_rho N l j n hn hρ)
  exact h.trans ((Complex.re_le_norm _).trans (hUpper N 1 one_pos n hn a ha ha1))

end ArtinMatthews
