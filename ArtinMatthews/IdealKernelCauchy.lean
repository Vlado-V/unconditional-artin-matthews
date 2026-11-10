module

public import ArtinMatthews.IdealFiniteFrame
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

/-! Finite weighted Hilbert--Schmidt Cauchy--Schwarz for arbitrary full
source and target tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B]

theorem idealKernel_bilinear_sq_le (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (K : A → B → ℂ) (f : A → ℂ) (g : B → ℂ) :
    ‖∑ a, ∑ b, ((μ a*ν b : ℝ) : ℂ) * K a b * f a * g b‖^2 ≤
      (∑ a, ∑ b, μ a*ν b*‖K a b‖^2) * idealFrameEnergy μ f * idealFrameEnergy ν g := by
  let w : A × B → ℝ := fun z => μ z.1*ν z.2
  have hw (z : A × B) : 0 ≤ w z := mul_nonneg (hμ z.1) (hν z.2)
  have hc := idealFrame_weighted_cauchy w hw (fun z => star (K z.1 z.2))
    (fun z => f z.1*g z.2)
  have he : (∑ z : A × B, (w z : ℂ) * star (star (K z.1 z.2)) * (f z.1*g z.2)) =
      ∑ a, ∑ b, ((μ a*ν b : ℝ) : ℂ) * K a b * f a * g b := by
    simp only [Fintype.sum_prod_type, w, star_star]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  have henergy : idealFrameEnergy w (fun z => f z.1*g z.2) =
      idealFrameEnergy μ f * idealFrameEnergy ν g := by
    simp only [idealFrameEnergy, w, Fintype.sum_prod_type, norm_mul, mul_pow, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  rw [he, henergy] at hc
  simpa only [idealFrameEnergy, Fintype.sum_prod_type, w, norm_star, mul_assoc] using hc

end
end ArtinMatthews
