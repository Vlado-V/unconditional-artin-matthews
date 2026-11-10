module

public import ArtinMatthews.CuspAverageProjectionBase
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralCuspVerticalTesting
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

/-! The exact primitive height change in the completed pairing. The true
width factor cancels the Jacobian of y=w*t and its hyperbolic density. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace ArtinMatthews

theorem spectralCuspVerticalMeasure_primitive_normalization {w Y : ℝ} (hw : 0<w) (hY : 0<Y)
    (F : ℝ → ℂ) :
    w • (∫ y, F (y/w) ∂cuspVerticalMeasure Y)=
      ∫ t in Ioi (Y/w), ((t^2:ℝ)⁻¹) • F t := by
  have hd : (∫ y, F (y/w) ∂cuspVerticalMeasure Y)=
      ∫ y in Ioi Y, ((y^2:ℝ)⁻¹) • F (y/w) := by
    simpa only [cuspHorizontalMeasure_univ,ENNReal.ofReal_one,one_smul,zpow_neg,zpow_ofNat] using
      cuspVerticalL2_integral_complex_density zero_lt_one hY (fun y => F (y/w))
  let G (t : ℝ) := ((t^2:ℝ)⁻¹) • F t
  have hFact : (∫ y in Ioi Y, ((y^2:ℝ)⁻¹) • F (y/w))=
      ∫ y in Ioi Y, ((w^2:ℝ)⁻¹) • G (y/w) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change Y<y at hy
    change ((y^2:ℝ)⁻¹) • F (y/w)=((w^2:ℝ)⁻¹) • (((y/w)^2:ℝ)⁻¹) • F (y/w)
    rw [smul_smul]
    congr 1
    field_simp [hw.ne',(hY.trans hy).ne']
  have hChange : (∫ y in Ioi Y, G (y/w))=w • ∫ t in Ioi (Y/w),G t := by
    simpa only [div_eq_mul_inv,inv_inv] using integral_comp_mul_right_Ioi G Y (inv_pos.mpr hw)
  rw [hd,hFact,integral_smul,hChange,smul_smul,smul_smul,
    show w*(w^2)⁻¹*w=1 by field_simp [hw.ne'],one_smul]

end ArtinMatthews
