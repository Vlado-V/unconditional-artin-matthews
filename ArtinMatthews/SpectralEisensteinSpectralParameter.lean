module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual Eisenstein eigenvalue lies in the proved ambient resolvent
region throughout its convergent half-plane. -/
noncomputable section
namespace ArtinMatthews

theorem eisensteinSpectralParameter_off_nonnegative_ray (s : ℂ) (hs : 1 < s.re) :
    (s*(1-s)).re < ‖s*(1-s)‖ := by
  have hre := Complex.re_le_norm (s*(1-s))
  have hn := norm_nonneg (s*(1-s))
  have hsq := Complex.sq_norm (s*(1-s))
  rw [Complex.normSq_apply] at hsq
  by_contra h
  have he : ‖s*(1-s)‖=(s*(1-s)).re := le_antisymm (not_lt.mp h) hre
  have hi : (s*(1-s)).im=0 := by nlinarith [sq_nonneg ((s*(1-s)).im)]
  have hsi : s.im=0 := by
    simp only [Complex.mul_im,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im] at hi
    nlinarith
  simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,hsi] at he
  nlinarith

end ArtinMatthews
