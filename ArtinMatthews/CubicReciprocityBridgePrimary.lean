module

public import ArtinMatthews.CubicReciprocityNonprincipalModel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Compatible primary generators in the two actual Eisenstein models. -/
noncomputable section

namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic

/-- Every Eisenstein prime away from three has a nonzero generator primary
in the concrete complex model used by the cubic numerator character. -/
theorem exists_cubicMoment_primary_generator (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ p ≠ 0 ∧
      CubicFirstMoment.primary (heckeIntegersEquivCubicEisenstein p) := by
  obtain ⟨p, hP, hp, _⟩ := cubicJacobi_exists_primary_generator P hg
  have hp0 : p ≠ 0 := by
    intro hzero
    have hP0 : P ≠ 0 := NeZero.ne P
    apply hP0
    rw [hP, hzero, Ideal.span_singleton_eq_bot.mpr rfl]
    rfl
  have h3lambda : (3 : O) ∣ lambda ^ 2 := by
    refine ⟨-omega, ?_⟩
    change (omega - 1) ^ 2 = 3 * -omega
    linear_combination omega_sq_for_norm
  have h3 : (3 : O) ∣ p - 1 := h3lambda.trans hp
  refine ⟨p, hP, hp0, ?_⟩
  change (3 : CubicFirstMoment.Eisenstein) ∣ heckeIntegersEquivCubicEisenstein p - 1
  simpa only [map_ofNat, map_sub, map_one] using
    map_dvd heckeIntegersEquivCubicEisenstein h3

end ArtinMatthews
