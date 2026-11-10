module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import ArtinMatthews.SpectralEisensteinVerticalCutoff
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! Complex Euler first integrals on a positive-height cusp ray. -/
namespace ArtinMatthews
noncomputable section
open Set

def cuspComplexEulerInvariant (c g : ℝ → ℂ) (p q : ℂ) (y : ℝ) : ℂ :=
  (y:ℂ)^(-p)*((y:ℂ)*g y-q*c y)

theorem cuspComplexEulerInvariant_hasDerivAt_zero (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y)
    {y : ℝ} (hy : Y<y) : HasDerivAt (cuspComplexEulerInvariant c g p q) 0 y := by
  have hy0 := lt_of_le_of_lt hY hy
  have hpow := eisensteinPositivePower_hasDerivAt (-p) y hy0
  have hu := (((hasDerivAt_id y).ofReal_comp.mul (hg y hy)).sub ((hc y hy).const_mul q))
  have H := hpow.mul hu
  have hn : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  convert H using 1
  · rfl
  · dsimp
    rw [Complex.cpow_sub (-p) 1 hn,Complex.cpow_one]
    field_simp
    linear_combination (y:ℂ)^(-p)*(y:ℂ)*g y*hpq-
      (y:ℂ)^(-p)*c y*hprod

theorem cuspComplexEulerInvariant_constant (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y)
    {x y : ℝ} (hx : Y<x) (hy : Y<y) :
    cuspComplexEulerInvariant c g p q x=cuspComplexEulerInvariant c g p q y := by
  have hd (z : ℝ) (hz : z ∈ Ioi Y) :=
    cuspComplexEulerInvariant_hasDerivAt_zero c g hY eig p q hpq hprod hc hg hz
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi Y).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy

end
end ArtinMatthews
