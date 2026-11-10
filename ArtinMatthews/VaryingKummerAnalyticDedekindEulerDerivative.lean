module

public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerLog
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Genuine differentiation of the locally uniformly convergent actual
Dedekind Euler logarithm. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Set

theorem dedekindEulerLog_hasSum_deriv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => deriv (dedekindEulerLocalLog K p) s)
      (deriv (dedekindEulerLog K) s) := by
  obtain ⟨σ, hσ, hσs⟩ := exists_between hs
  exact Complex.hasSum_deriv_of_summable_norm (dedekindEulerLogMajorant_summable K hσ)
    (fun p => (dedekindEulerLocalLog_differentiableOn K p).mono (fun z hz => hσ.trans hz))
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun p z hz => dedekindEulerLocalLog_norm_le K p hσ.le (le_of_lt hz)) hσs

theorem dedekindZeta_logDeriv_hasSum_deriv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => deriv (dedekindEulerLocalLog K p) s)
      (logDeriv (NumberField.dedekindZeta K) s) := by
  rw [dedekindZeta_logDeriv_eq_deriv_eulerLog K hs]
  exact dedekindEulerLog_hasSum_deriv K hs

end ArtinMatthews.VaryingKummerAnalytic
