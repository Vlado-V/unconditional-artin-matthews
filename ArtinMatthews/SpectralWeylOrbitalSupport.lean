module

public import ArtinMatthews.SpectralOrbitalWeylKernel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! A genuine modulus cutoff for compact positive-height orbital tests. -/

noncomputable section
open Set MeasureTheory Filter Matrix
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem realWeylMatrix_coe_smul (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane) :
    ((realWeylMatrix c hc • z : UpperHalfPlane) : ℂ) =
      ((-((c^2)⁻¹) : ℝ) : ℂ) * (z : ℂ)⁻¹ := by
  have hz : (z : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    exact z.im_pos.ne' (by simpa using hi)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [realWeylMatrix,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Algebra.algebraMap_self_apply,Complex.ofReal_zero,
    zero_mul,zero_add,add_zero,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hc,hz]

theorem realWeylMatrix_im (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane) :
    (realWeylMatrix c hc • z).im = z.im / (c^2 * Complex.normSq (z : ℂ)) := by
  have h := congrArg Complex.im (realWeylMatrix_coe_smul c hc z)
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    Complex.inv_im] at h
  change (realWeylMatrix c hc • z).im = -(c^2)⁻¹ * (-z.im / Complex.normSq (z : ℂ)) at h
  rw [h]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

theorem realWeylMatrix_height_product_le (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane) :
    (realWeylMatrix c hc • z).im * c^2 * z.im ≤ 1 := by
  have hz : (z : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    exact z.im_pos.ne' (by simpa using hi)
  have hn : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.mpr hz
  have he := (div_eq_iff (mul_ne_zero (pow_ne_zero 2 hc) hn.ne')).mp (realWeylMatrix_im c hc z).symm
  have hnorm : z.im^2 ≤ Complex.normSq (z : ℂ) := by
    change (z : ℂ).im^2 ≤ Complex.normSq (z : ℂ)
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (z : ℂ).re]
  have hprod := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ (realWeylMatrix c hc • z).im * c^2 by positivity)
  apply (mul_le_mul_iff_right₀ z.im_pos).mp
  nlinarith [he]

theorem cuspWeylOrbitalIntegrand_modulus_bound (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ : Function.support ρ ⊆ Ici a) (hη : Function.support η ⊆ Ici b)
    (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane)
    (hz : cuspWeylOrbitalIntegrand N m n ρ η c hc z ≠ 0) : c^2*a*b ≤ 1 := by
  have hr : ρ z.im ≠ 0 := by
    intro h
    apply hz
    simp [cuspWeylOrbitalIntegrand,cuspFourierWave,h]
  have he : η (realWeylMatrix c hc • z).im ≠ 0 := by
    intro h
    apply hz
    simp [cuspWeylOrbitalIntegrand,cuspFourierWave,h]
  have hay : a ≤ z.im := hρ hr
  have hby : b ≤ (realWeylMatrix c hc • z).im := hη he
  have hab := mul_le_mul hay hby hb.le (ha.le.trans hay)
  calc
    c^2*a*b = c^2*(a*b) := by ring
    _ ≤ c^2*(z.im*(realWeylMatrix c hc • z).im) :=
      mul_le_mul_of_nonneg_left hab (sq_nonneg c)
    _ = (realWeylMatrix c hc • z).im*c^2*z.im := by ring
    _ ≤ 1 := realWeylMatrix_height_product_le c hc z

theorem cuspWeylOrbitalKernel_eq_zero_of_large_modulus (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ : Function.support ρ ⊆ Ici a) (hη : Function.support η ⊆ Ici b)
    (c : ℝ) (hc : c ≠ 0) (hlarge : 1 < c^2*a*b) :
    cuspWeylOrbitalKernel N m n ρ η c hc = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  simp only [Pi.zero_apply]
  by_contra hz
  exact (not_le_of_gt hlarge) (cuspWeylOrbitalIntegrand_modulus_bound N m n ρ η a b ha hb hρ hη c hc z hz)

end ArtinMatthews
