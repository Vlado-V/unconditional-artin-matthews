module

public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact cutoff differentiation identities for the quantitative H2 estimate. -/
noncomputable section
open scoped ContDiff
open OAI.Analysis.PDE.Weak
namespace ArtinMatthews

theorem spectral_coordinateDerivative_mul {F G : (Fin 2 → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    coordinateDerivative (fun x => F x*G x) j =
      fun x => coordinateDerivative F j x*G x+F x*coordinateDerivative G j x := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_fun_mul (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem spectral_coordinateDerivative_add {F G : (Fin 2 → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    coordinateDerivative (fun x => F x+G x) j =
      fun x => coordinateDerivative F j x+coordinateDerivative G j x := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_fun_add (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)]
  rfl

theorem spectral_coordinate_mixed_cutoff_square {η u : (Fin 2 → ℝ) → ℝ}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x : Fin 2 → ℝ) :
    coordinateDerivative (coordinateDerivative (η*(η*u)) 0) 1 x =
      η x*coordinateDerivative (η*coordinateDerivative u 0) 1 x +
      η x*coordinateDerivative η 1 x*coordinateDerivative u 0 x +
      2*η x*coordinateDerivative η 0 x*coordinateDerivative u 1 x +
      2*(coordinateDerivative η 1 x*coordinateDerivative η 0 x+
        η x*coordinateDerivative (coordinateDerivative η 0) 1 x)*u x := by
  have hη0 := contDiff_coordinateDerivative hη (0 : Fin 2)
  have hu0 := contDiff_coordinateDerivative hu (0 : Fin 2)
  simp only [Pi.mul_def]
  simp (disch := fun_prop) only [spectral_coordinateDerivative_mul,spectral_coordinateDerivative_add]
  ring

end ArtinMatthews
