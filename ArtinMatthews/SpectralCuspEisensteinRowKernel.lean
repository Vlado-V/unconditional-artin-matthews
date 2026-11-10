module

public import ArtinMatthews.SpectralCuspEisensteinCoordinates
public import ArtinMatthews.SpectralCuspEisensteinIntegral
public import ArtinMatthews.SpectralEisensteinRowKernel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized target-cusp rows unfold over the integer lattice;
source and target widths both remain explicit in the resulting coefficient. -/
noncomputable section
open Set Matrix MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinCoordinateTerm_eq (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (d : CuspEisensteinRowFibre N r a c.val) (x : ℝ) :
    cuspEisensteinRowTerm N r a s (cuspEisensteinPositiveCoordinateRow N r a ⟨c,d⟩).val
      (cuspEisensteinTargetPoint N r y hy x)=
      (gamma0CuspTrueWidth N r:ℂ)^s*eisensteinRealRowTerm s
        ((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ)) d.val x y := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hcoe : ((cuspEisensteinTargetPoint N r y hy x):ℂ)=Complex.mk (w*x) (w*y) := by
    rw [cuspEisensteinTargetPoint,cuspWidthDilation_coe_smul]
    apply Complex.ext <;> simp [w,gamma0EisensteinHorizontalPoint]
  have him : (cuspEisensteinTargetPoint N r y hy x).im=w*y :=
    cuspWidthDilation_im_smul _ _ _
  have hn : ‖(c.val:ℂ)*Complex.mk (w*x) (w*y)+(d.val:ℂ)‖^2=
      (((c.val:ℝ)*w)*x+d.val)^2+(((c.val:ℝ)*w)*y)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,pow_two]
    ring
  rw [cuspEisensteinRowTerm,cuspEisensteinRowHeight_row,him,hcoe]
  change ((w*y/‖(c.val:ℂ)*Complex.mk (w*x) (w*y)+(d.val:ℂ)‖^2:ℝ):ℂ)^s=_
  rw [hn]
  have he : w*y/((((c.val:ℝ)*w)*x+d.val)^2+(((c.val:ℝ)*w)*y)^2)=
      w*(y/((((c.val:ℝ)*w)*x+d.val)^2+(((c.val:ℝ)*w)*y)^2)) := by ring
  rw [he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by dsimp [w]; positivity) (by positivity)]
  rfl

theorem cuspEisenstein_width_power (s : ℂ) (u c : ℝ) (hu : 0 < u) (hc : 0 < c) :
    (u:ℂ)^s*((c*u:ℝ):ℂ)^(-2*s)=(u:ℂ)^(-s)*(c:ℂ)^(-2*s) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hc.le hu.le]
  calc
    _=(u:ℂ)^s*(u:ℂ)^(-2*s)*(c:ℂ)^(-2*s) := by ring
    _=_ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
      congr 2
      ring

def cuspEisensteinCoordinateIntegral (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (d : CuspEisensteinRowFibre N r a c.val) : ℂ :=
  cuspEisensteinRowIntegral N r a s y hy (cuspEisensteinPositiveCoordinateRow N r a ⟨c,d⟩).val

theorem cuspEisensteinCoordinateIntegral_eq (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (d : CuspEisensteinRowFibre N r a c.val) :
    cuspEisensteinCoordinateIntegral N r a s y hy c d=
      (gamma0CuspTrueWidth N r:ℂ)^s*∫ x in (0:ℝ)..1,
        eisensteinRealRowTerm s ((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ)) d.val x y := by
  unfold cuspEisensteinCoordinateIntegral cuspEisensteinRowIntegral
  simp_rw [cuspEisensteinCoordinateTerm_eq]
  rw [integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

theorem cuspEisensteinCoordinateIntegral_orbit (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (c : {c : ℕ // 0 < c})
    (b : CuspEisensteinRowResidues N r a c.val) :
    (∑' k : ℤ, cuspEisensteinCoordinateIntegral N r a s y hy c
      (cuspEisensteinResidueTranslate N r a c.val (b,k)))=
      (gamma0CuspTrueWidth N r:ℂ)^(-s)*(c.val:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
        ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
  have hc : 0 < (c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ) := mul_pos
    (by exact_mod_cast c.property) (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
  simp only [cuspEisensteinCoordinateIntegral_eq,cuspEisensteinResidueTranslate,
    Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [tsum_mul_left]
  have he : (fun k : ℤ => ∫ x in (0:ℝ)..1,
      eisensteinRealRowTerm s ((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ))
        ((b.val.val:ℝ)+(gamma0CuspTrueWidth N r:ℝ)*c.val*k) x y)=
      fun k : ℤ => ∫ x in (0:ℝ)..1,
        eisensteinRealRowTerm s ((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ))
          ((b.val.val:ℝ)+((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ))*k) x y := by
    funext k
    congr 1
    funext x
    congr 1
    ring
  rw [he,eisensteinRealRowTerm_translate_integral s (by linarith) _ hc _ y hy]
  rw [← mul_assoc,← mul_assoc]
  have hp := cuspEisenstein_width_power s (gamma0CuspTrueWidth N r:ℝ) (c.val:ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r) (by exact_mod_cast c.property)
  have hp' : (gamma0CuspTrueWidth N r:ℂ)^s*
      (((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^(-2*s)=
      (gamma0CuspTrueWidth N r:ℂ)^(-s)*(c.val:ℂ)^(-2*s) := by
    simpa only [Complex.ofReal_natCast] using hp
  rw [hp']

end ArtinMatthews
