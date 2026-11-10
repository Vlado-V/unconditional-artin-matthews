module

public import ArtinMatthews.SourceArchSphericalSection
public import ArtinMatthews.SourceKPAdelicUpper
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchUpperDenominator (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  ‖g 1 0‖^2 + ‖g 1 1 + (t : ℂ)*(g 1 0*z)‖^2

def sourceArchUpperDenominatorOne (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  2 * (star (g 1 1 + (t : ℂ)*(g 1 0*z)) * (g 1 0*z)).re

def sourceArchUpperDenominatorTwo (g : GL (Fin 2) ℂ) (z : ℂ) : ℝ :=
  2 * ‖g 1 0*z‖^2

theorem sourceArchBottomNorm_right_upper (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    sourceArchBottomNorm (g * sourceKPUpperMatrix ℂ ((t : ℂ)*z)) =
      sourceArchUpperDenominator g z t := by
  have h0 : (g * sourceKPUpperMatrix ℂ ((t : ℂ)*z)) 1 0 = g 1 0 := by
    change ((g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, (t : ℂ)*z; 0, 1]) 1 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (g * sourceKPUpperMatrix ℂ ((t : ℂ)*z)) 1 1 =
      g 1 1 + (t : ℂ)*(g 1 0*z) := by
    change ((g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, (t : ℂ)*z; 0, 1]) 1 1 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [sourceArchBottomNorm, h0, h1]
  rfl

theorem sourceArchUpperDenominator_pos (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    0 < sourceArchUpperDenominator g z t := by
  rw [← sourceArchBottomNorm_right_upper]
  exact sourceArchBottomNorm_pos _

theorem sourceArchHeight_right_upper (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    sourceArchHeight (g * sourceKPUpperMatrix ℂ ((t : ℂ)*z)) =
      ‖(GeneralLinearGroup.det g : ℂ)‖ / sourceArchUpperDenominator g z t := by
  have hd : GeneralLinearGroup.det (sourceKPUpperMatrix ℂ ((t : ℂ)*z)) = 1 := by
    apply Units.ext
    simp [sourceKPUpperMatrix, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  rw [sourceArchHeight, map_mul, hd, mul_one, sourceArchBottomNorm_right_upper]

theorem sourceArchUpperDenominator_hasDerivAt (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceArchUpperDenominator g z) (sourceArchUpperDenominatorOne g z t) t := by
  let a := g 1 0*z
  let d := g 1 1
  have he : sourceArchUpperDenominator g z = fun x : ℝ =>
      ‖g 1 0‖^2 + ((d.re+x*a.re)^2+(d.im+x*a.im)^2) := by
    funext x
    simp [sourceArchUpperDenominator, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      a, d, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have hv : sourceArchUpperDenominatorOne g z t =
      2*(d.re+t*a.re)*a.re + 2*(d.im+t*a.im)*a.im := by
    simp [sourceArchUpperDenominatorOne, a, d, Complex.mul_re, Complex.mul_im]
    ring
  have hraw : HasDerivAt (fun x : ℝ =>
      ‖g 1 0‖^2 + ((d.re+x*a.re)^2+(d.im+x*a.im)^2))
      (2*(d.re+t*a.re)*a.re + 2*(d.im+t*a.im)*a.im) t := by
    simpa [Pi.pow_apply, Pi.add_apply] using!
      (((((hasDerivAt_id t).mul_const a.re).const_add d.re).pow 2).add
        ((((hasDerivAt_id t).mul_const a.im).const_add d.im).pow 2)).const_add (‖g 1 0‖^2)
  rw [he]
  rw [hv]
  exact hraw

theorem sourceArchUpperDenominatorOne_hasDerivAt (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceArchUpperDenominatorOne g z) (sourceArchUpperDenominatorTwo g z) t := by
  let a := g 1 0*z
  let d := g 1 1
  have he : sourceArchUpperDenominatorOne g z = fun x : ℝ =>
      2*((d.re+x*a.re)*a.re+(d.im+x*a.im)*a.im) := by
    funext x
    simp [sourceArchUpperDenominatorOne, a, d, Complex.mul_re, Complex.mul_im]
    ring
  have hv : sourceArchUpperDenominatorTwo g z = 2*(a.re*a.re+a.im*a.im) := by
    simp only [sourceArchUpperDenominatorTwo, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rfl
  have hraw : HasDerivAt (fun x : ℝ => 2*((d.re+x*a.re)*a.re+(d.im+x*a.im)*a.im))
      (2*(a.re*a.re+a.im*a.im)) t := by
    simpa [Pi.add_apply] using!
      (((((hasDerivAt_id t).mul_const a.re).const_add d.re).mul_const a.re).add
        ((((hasDerivAt_id t).mul_const a.im).const_add d.im).mul_const a.im)).const_mul 2
  rw [he]
  rw [hv]
  exact hraw

theorem sourceArchUpperDenominatorOne_bound (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    |sourceArchUpperDenominatorOne g z t| ≤ ‖z‖ * sourceArchUpperDenominator g z t := by
  let w := g 1 1+(t : ℂ)*(g 1 0*z)
  have h := Complex.abs_re_le_norm (star w*(g 1 0*z))
  simp only [norm_mul, norm_star] at h
  have hs : 2*‖g 1 0‖*‖w‖ ≤ ‖g 1 0‖^2+‖w‖^2 := by nlinarith [sq_nonneg (‖g 1 0‖-‖w‖)]
  calc
    |sourceArchUpperDenominatorOne g z t| = 2*|(star w*(g 1 0*z)).re| := by
      simp [sourceArchUpperDenominatorOne, w, abs_mul]
    _ ≤ 2*(‖w‖*(‖g 1 0‖*‖z‖)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ‖z‖*(2*‖g 1 0‖*‖w‖) := by ring
    _ ≤ ‖z‖*(‖g 1 0‖^2+‖w‖^2) := mul_le_mul_of_nonneg_left hs (norm_nonneg z)
    _ = _ := rfl

theorem sourceArchUpperDenominatorTwo_nonneg (g : GL (Fin 2) ℂ) (z : ℂ) :
    0 ≤ sourceArchUpperDenominatorTwo g z := by
  unfold sourceArchUpperDenominatorTwo
  positivity

theorem sourceArchUpperDenominatorTwo_bound (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    sourceArchUpperDenominatorTwo g z ≤ 2*‖z‖^2*sourceArchUpperDenominator g z t := by
  have h : ‖g 1 0‖^2 ≤ sourceArchUpperDenominator g z t := by
    unfold sourceArchUpperDenominator
    exact le_add_of_nonneg_right (sq_nonneg _)
  simpa only [sourceArchUpperDenominatorTwo, norm_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm]
    using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*‖z‖^2)

end
end ArtinMatthews.SourceArchJacquet
