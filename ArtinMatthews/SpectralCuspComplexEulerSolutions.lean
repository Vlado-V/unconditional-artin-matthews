module

public import ArtinMatthews.SpectralCuspComplexEulerInvariant
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

/-! The actual two complex-power solution space of the cusp Euler equation,
with constants obtained from genuine first integrals. -/
namespace ArtinMatthews
noncomputable section

theorem cuspComplexEuler_firstOrder_identity (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y)
    {y : ℝ} (hy : Y<y) :
    (y:ℂ)*g y-q*c y=(y:ℂ)^p*cuspComplexEulerInvariant c g p q (Y+1) := by
  have H := cuspComplexEulerInvariant_constant c g hY eig p q hpq hprod hc hg hy
    (by linarith : Y<Y+1)
  have hn : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (lt_of_le_of_lt hY hy).ne'
  have he : (y:ℂ)^p*(y:ℂ)^(-p)=1 := by
    rw [Complex.cpow_neg,mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hn))]
  calc
    _=((y:ℂ)^p*(y:ℂ)^(-p))*((y:ℂ)*g y-q*c y) := by rw [he,one_mul]
    _=(y:ℂ)^p*cuspComplexEulerInvariant c g p q (Y+1) := by
      rw [mul_assoc]
      exact congrArg (fun v : ℂ => (y:ℂ)^p*v) H

theorem cuspComplexEuler_solution_formula (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig) (hne : p≠q)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y)
    {y : ℝ} (hy : Y<y) :
    c y=((y:ℂ)^p*cuspComplexEulerInvariant c g p q (Y+1)-
      (y:ℂ)^q*cuspComplexEulerInvariant c g q p (Y+1))/(p-q) := by
  have hp := cuspComplexEuler_firstOrder_identity c g hY eig p q hpq hprod hc hg hy
  have hq := cuspComplexEuler_firstOrder_identity c g hY eig q p
    (by rw [add_comm];exact hpq) (by rw [mul_comm];exact hprod) hc hg hy
  apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr
  calc
    _=((y:ℂ)*g y-q*c y)-((y:ℂ)*g y-p*c y) := by ring
    _=_ := by rw [hp,hq]

theorem cuspComplexEuler_solution_classification (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig) (hne : p≠q)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y) :
    ∃ A B : ℂ, ∀ y>Y, c y=A*(y:ℂ)^p+B*(y:ℂ)^q := by
  refine ⟨cuspComplexEulerInvariant c g p q (Y+1)/(p-q),
    -cuspComplexEulerInvariant c g q p (Y+1)/(p-q),?_⟩
  intro y hy
  rw [cuspComplexEuler_solution_formula c g hY eig p q hpq hprod hne hc hg hy]
  ring

end
end ArtinMatthews
