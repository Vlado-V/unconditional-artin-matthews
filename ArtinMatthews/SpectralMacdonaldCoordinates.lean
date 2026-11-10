module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

/-! The genuine hyperbolic addition geometry behind the Macdonald
product integral; no Bessel product identity is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace ArtinMatthews

def spectralMacdonaldRadius (x y w : ℝ) : ℝ :=
  Real.sqrt ((x+y*Real.exp w)*(x+y*Real.exp (-w)))

def spectralMacdonaldShift (x y w : ℝ) : ℝ :=
  Real.log ((x+y*Real.exp w)/spectralMacdonaldRadius x y w)

theorem spectralMacdonaldRadius_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℝ) :
    0 < spectralMacdonaldRadius x y w := by
  apply Real.sqrt_pos.mpr
  exact mul_pos (add_pos hx (mul_pos hy (Real.exp_pos w)))
    (add_pos hx (mul_pos hy (Real.exp_pos (-w))))

theorem spectralMacdonaldRadius_sq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℝ) :
    spectralMacdonaldRadius x y w ^ 2 = x^2+y^2+2*x*y*Real.cosh w := by
  unfold spectralMacdonaldRadius
  rw [Real.sq_sqrt (le_of_lt (mul_pos (add_pos hx (mul_pos hy (Real.exp_pos w)))
    (add_pos hx (mul_pos hy (Real.exp_pos (-w)))))),Real.cosh_eq,Real.exp_neg]
  field_simp
  ring

theorem spectralMacdonaldShift_exp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℝ) :
    Real.exp (spectralMacdonaldShift x y w) = (x+y*Real.exp w)/spectralMacdonaldRadius x y w := by
  apply Real.exp_log
  exact div_pos (add_pos hx (mul_pos hy (Real.exp_pos w))) (spectralMacdonaldRadius_pos hx hy w)

theorem spectralMacdonaldShift_exp_neg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℝ) :
    Real.exp (-spectralMacdonaldShift x y w) = (x+y*Real.exp (-w))/spectralMacdonaldRadius x y w := by
  have hP : x+y*Real.exp w ≠ 0 := (add_pos hx (mul_pos hy (Real.exp_pos w))).ne'
  have hR : spectralMacdonaldRadius x y w ≠ 0 := (spectralMacdonaldRadius_pos hx hy w).ne'
  have hs : spectralMacdonaldRadius x y w ^ 2 = (x+y*Real.exp w)*(x+y*Real.exp (-w)) := by
    exact Real.sq_sqrt (le_of_lt (mul_pos (add_pos hx (mul_pos hy (Real.exp_pos w)))
      (add_pos hx (mul_pos hy (Real.exp_pos (-w))))))
  rw [Real.exp_neg,spectralMacdonaldShift_exp hx hy]
  field_simp
  nlinarith [hs]

theorem spectralMacdonald_cosh_shift {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w u : ℝ) :
    x*Real.cosh u+y*Real.cosh (w-u) =
      spectralMacdonaldRadius x y w*Real.cosh (u-spectralMacdonaldShift x y w) := by
  rw [Real.cosh_eq,Real.cosh_eq,Real.cosh_eq]
  have h1 : Real.exp (u-spectralMacdonaldShift x y w) =
      Real.exp u*Real.exp (-spectralMacdonaldShift x y w) := by rw [sub_eq_add_neg,Real.exp_add]
  have h2 : Real.exp (-(u-spectralMacdonaldShift x y w)) =
      Real.exp (-u)*Real.exp (spectralMacdonaldShift x y w) := by
    rw [show -(u-spectralMacdonaldShift x y w) = -u+spectralMacdonaldShift x y w by ring,Real.exp_add]
  have h3 : Real.exp (w-u) = Real.exp w*Real.exp (-u) := by rw [sub_eq_add_neg,Real.exp_add]
  have h4 : Real.exp (-(w-u)) = Real.exp (-w)*Real.exp u := by
    rw [show -(w-u) = -w+u by ring,Real.exp_add]
  rw [h1,h2,h3,h4,
    spectralMacdonaldShift_exp hx hy,spectralMacdonaldShift_exp_neg hx hy]
  have hR : spectralMacdonaldRadius x y w ≠ 0 := (spectralMacdonaldRadius_pos hx hy w).ne'
  field_simp
  ring

end ArtinMatthews
