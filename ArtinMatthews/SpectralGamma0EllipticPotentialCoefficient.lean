module

public import ArtinMatthews.SpectralGamma0EllipticPotentialFunction
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! A globally smooth bounded multiplication operator which agrees with
the actual eigenfunction potential on the cutoff plateau. -/
noncomputable section
open Set
open scoped ContDiff
open OAI.Analysis.PDE.Weak
namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

def spectralEllipticPotentialCoefficient (lam : ℝ) :
    (Fin 2 → ℝ) → ℝ →L[ℝ] ℝ :=
  fun x => spectralEllipticPotentialFunction φ ha hφ lam x • ContinuousLinearMap.id ℝ ℝ

theorem spectralEllipticPotentialCoefficient_smoothBounded (lam : ℝ) :
    SmoothBounded (spectralEllipticPotentialCoefficient φ ha hφ lam) :=
  smoothBounded_of_hasCompactSupport
    ((spectralEllipticPotentialFunction_smooth φ ha hφ lam).smul contDiff_const)
    ((spectralEllipticPotentialFunction_compact φ ha hφ lam).smul_right)

theorem spectralEllipticPotentialCoefficient_apply_eq (lam : ℝ) {x : Fin 2 → ℝ}
    (hx : 0 < x 1) (hplateau : φ (spectralEllipticCoordinates x) = 1) (u : ℝ) :
    spectralEllipticPotentialCoefficient φ ha hφ lam x u = lam / (x 1)^2 * u := by
  change spectralEllipticPotentialFunction φ ha hφ lam x * u = _
  rw [spectralEllipticPotentialFunction_eq φ ha hφ lam hx hplateau]

end ArtinMatthews
