module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.ModularForms.Petersson
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The genuine Petersson self-pair is the real physical weighted norm. -/
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralPetersson_self_pair (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) F F z = (‖F z‖^2*z.im^k : ℝ) := by
  rw [UpperHalfPlane.petersson,zpow_natCast,← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem spectralPetersson_self_integrable (k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Integrable (fun z => UpperHalfPlane.petersson (k : ℤ) F F z)) :
    Integrable (fun z => ‖F z‖^2*z.im^k) := by
  have h := hF.norm
  simpa only [spectralPetersson_self_pair,Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (UpperHalfPlane.im_pos _).le _))] using h

end ArtinMatthews
