module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal frequency dilation preserves dx/x; no hidden frequency or
cusp-width scalar is absorbed into the KL normalization. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralKLPhysical_dilation_integral (F : ℝ → ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), F (x/q)/(x : ℂ)) = ∫ y in Ioi (0 : ℝ), F y/(y : ℂ) := by
  have h := integral_comp_mul_left_Ioi' (fun x : ℝ => F (x/q)/(x : ℂ)) 0 hq
  simp only [mul_zero] at h
  calc
    _ = q • ∫ y in Ioi (0 : ℝ), F (q*y/q)/((q*y : ℝ) : ℂ) := h.symm
    _ = _ := by
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [Complex.real_smul,mul_div_cancel_left₀ y hq.ne',Complex.ofReal_mul]
      have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
      field_simp

theorem spectralKLPhysical_dilation_real_integral (F : ℝ → ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), F (x/q)/x) = ∫ y in Ioi (0 : ℝ), F y/y := by
  have h := spectralKLPhysical_dilation_integral (fun x => (F x : ℂ)) hq
  have hc : (∫ x in Ioi (0 : ℝ), (F (x/q) : ℂ)/(x : ℂ)) =
      ((∫ x in Ioi (0 : ℝ), F (x/q)/x : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_div]
    exact integral_complex_ofReal
  have hc' : (∫ y in Ioi (0 : ℝ), (F y : ℂ)/(y : ℂ)) =
      ((∫ y in Ioi (0 : ℝ), F y/y : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_div]
    exact integral_complex_ofReal
  rw [hc,hc'] at h
  exact Complex.ofReal_injective h

end ArtinMatthews
