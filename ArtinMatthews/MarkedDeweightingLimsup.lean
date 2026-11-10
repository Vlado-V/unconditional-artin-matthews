module

public import ArtinMatthews.MarkedActualDeweighting
public import ArtinMatthews.MarkedDeweightingParameter
public import ArtinMatthews.MarkedLimsupScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The exact normalized limsup form of positive prime deweighting. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

noncomputable def markedPrimeDeweightingError {J I : Type*}
    [Fintype J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (Φ : ℝ → ℝ) (T : ℝ) (F : ℝ → ℕ → ℂ) (x : ℝ) : ℝ :=
  ‖∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
    (Φ ((u : ℝ) / x) : ℂ) * F x u *
      (markedArrayDeviation (fun j i => markedLogPowerBand (e j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u : ℂ)‖

/-- Equation (2.10), with a concrete constant independent of the number
of arrays and of their fixed exponents. Bounds on the test coefficients
are required only at prime predecessors. -/
theorem marked_actual_prime_deweighting_limsup {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0)
    (F : ℝ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u + 1).Prime → ‖F x u‖ ≤ C) :
    limsup (fun x => Real.log x / x * markedPrimeDeweightingError e Φ T F x) atTop ≤
      C * markedPrimeDeweightingConstant (Fintype.card I) (1 / 960048) 20000 Φ T /
        Real.sqrt (Fintype.card J) := by
  apply marked_normalized_limsup_le
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact marked_actual_prime_deweighting_canonical e he hinj hJ
      Φ hT ha hΦ hderiv hΦT hΦ0 hlow F hC hF

/-- The constant in the exact prime-deweighting limsup tends to zero as
the number of arrays increases, while the number of bands stays fixed. -/
theorem marked_prime_deweighting_limsup_constant_decay (K : ℕ)
    (Φ : ℝ → ℝ) (T C : ℝ) :
    Tendsto (fun b : ℕ => C * markedPrimeDeweightingConstant K (1 / 960048) 20000 Φ T /
      Real.sqrt b) atTop (𝓝 0) :=
  marked_deweighting_array_count_decay _

end ArtinMatthews
