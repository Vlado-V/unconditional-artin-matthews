module

public import ArtinMatthews.SpectralGamma0EllipticCompletion
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
public import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient


set_option backward.privateInPublic true
@[expose] public section

/-! The completed localized gradient is the actual distributional derivative
of its localized value.  The source theorem is applied to the proved native
graph-closure membership, not to an assumed weak derivative. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

theorem gamma0EllipticPair_weak_derivative
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ) (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (j : Fin 2) (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) :
    (∫ x : Fin 2 → ℝ, ((gamma0EllipticPair φ ha hφ r L N u).2 x) j * χ x) =
      -(∫ x : Fin 2 → ℝ, (gamma0EllipticPair φ ha hφ r L N u).1 x *
        fderiv ℝ χ x (Pi.single j 1)) :=
  H1Zero.weak_derivative (gamma0EllipticPair_mem_H1Zero φ ha hφ r L N u) j χ hχ hcχ

end ArtinMatthews
