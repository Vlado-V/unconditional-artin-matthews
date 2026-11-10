module

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
public import ArtinMatthews.SpectralGamma0EllipticInteriorH2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! A linear version of the genuine quantitative interior H2 estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem spectralElliptic_laplacian_interior_H2_linear_bound
    (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
    (f : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))) {Ω : Set (Fin 2 → ℝ)}
    (hΩ : IsOpen Ω) (hweak : WeakDivergenceEquation Ω p.2 f)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {K L : ℝ} (hK : 0 ≤ K) (_hL : 0 ≤ L) (hηM : ∀ x, |η x| ≤ 1)
    (hηK : ∀ x, ‖cellGradient η x‖ ≤ K) (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (hsη : tsupport η ⊆ Ω) (j : Fin 2) :
    ∃ g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)),
      ‖g‖ ≤ ‖f‖+(4*K+L)*‖p.2‖ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffL2 η hη.continuous hηM p.2) g := by
  obtain ⟨g,hg,hd⟩ := spectralElliptic_laplacian_interior_H2 p hp f hΩ hweak
    η hη hcη hK hηM hηK hηL hsη j
  refine ⟨g,hg.trans ?_,hd⟩
  have hroot : Real.sqrt ((‖f‖+2*(K*‖p.2‖))^2+4*‖f‖*(K*‖p.2‖)) ≤
      ‖f‖+4*K*‖p.2‖ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (K*‖p.2‖)]
  nlinarith

end ArtinMatthews
