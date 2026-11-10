module

public import ArtinMatthews.SpectralABLOppositeKTransform
public import ArtinMatthews.SpectralABLCoshHeightWeight
public import ArtinMatthews.SpectralABLOppositeCosine
public import ArtinMatthews.SpectralCompactLaplaceDecay
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

theorem spectral_sinh_abs_eq_abs_sinh (u : ℝ) : Real.sinh |u| = |Real.sinh u| := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu,abs_of_nonneg (Real.sinh_nonneg_iff.mpr hu)]
  · have hu' := lt_of_not_ge hu
    rw [abs_of_neg hu',Real.sinh_neg,abs_of_nonpos (Real.sinh_nonpos_iff.mpr hu'.le)]

/-- Uniform base estimate for the literal source test, expressed in
compact spatial derivative masses. -/
theorem spectralABLOppositeTransform_base_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (z : ℂ) (hz : |z.im| ≤ 1/2) (b : ℝ) (hb : 0 < b) (hb₁ : b ≤ 1) :
    let g := spectralKLPhysicalCompactDiv f
    ‖spectralABLOppositeTransform f z‖ ≤
      (16/Real.pi)*((∫ x : ℝ, ‖g x‖)+b^3*(∫ x : ℝ, ‖iteratedDeriv 3 g x‖))*
        (1+Real.log (4/b))*Real.exp (2*|z.im| *Real.log (4/b)) := by
  let g := spectralKLPhysicalCompactDiv f
  let M := (∫ x : ℝ, ‖g x‖)+b^3*(∫ x : ℝ, ‖iteratedDeriv 3 g x‖)
  let r := 2*|z.im|
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (mul_nonneg (pow_nonneg hb.le _) (integral_nonneg fun _ => norm_nonneg _))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r ≤ 1 := by dsimp [r]; linarith
  have hg := spectralKLPhysicalCompactDiv_smooth f hf hp
  have hgc := spectralKLPhysicalCompactDiv_hasCompactSupport f hc
  have hgp : tsupport g ⊆ Ici (0 : ℝ) := (spectralKLPhysicalCompactDiv_tsupport f).trans
    (hp.trans Ioi_subset_Ici_self)
  have hφ (u : ℝ) :
      ‖spectralABLOppositeCosineProfile f u‖ ≤ 8*M/(1+b*Real.sinh |u|)^3 := by
    let w : ℂ := (Real.sinh u : ℂ)*I
    let D := (1+b*Real.sinh |u|)^3
    have hD : 0 < D := by
      dsimp [D]
      have hs := Real.sinh_nonneg_iff.mpr (abs_nonneg u)
      positivity
    have hw : ‖w‖ = Real.sinh |u| := by
      simp only [w,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
        spectral_sinh_abs_eq_abs_sinh]
    have hwre : w.re = 0 := by simp [w,Complex.mul_re]
    have hp' : ‖spectralCompactLaplace g w‖ ≤ 8*M/D := (le_div_iff₀ hD).mpr (by
      simpa only [hw,D,M,mul_comm,show (2 : ℝ)^3 = 8 by norm_num] using
        spectralCompactLaplace_scaled_norm_le g hg hgc hgp 3 hb.le (show 0 ≤ w.re by rw [hwre]))
    have hm' : ‖spectralCompactLaplace g (-w)‖ ≤ 8*M/D := (le_div_iff₀ hD).mpr (by
      simpa only [norm_neg,hw,D,M,mul_comm,show (2 : ℝ)^3 = 8 by norm_num] using
        spectralCompactLaplace_scaled_norm_le g hg hgc hgp 3 hb.le
          (show 0 ≤ (-w).re by simp [hwre]))
    have he : spectralCompactLaplace g w+spectralCompactLaplace g (-w) =
        2*spectralABLOppositeCosineProfile f u :=
      spectralCompactLaplace_sinh_pair g hg.continuous hgc u
    have hsum := (norm_add_le (spectralCompactLaplace g w) (spectralCompactLaplace g (-w))).trans
      (add_le_add hp' hm')
    rw [he,norm_mul,show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] at hsum
    linarith
  have hE (u : ℝ) : ‖Complex.exp (2*I*z*(u : ℂ))‖ ≤ Real.exp (r*|u|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have he : (2*I*z*(u : ℂ)).re = -(2*z.im*u) := by
      norm_num [Complex.mul_re,Complex.mul_im]
    rw [he]
    calc
      _ ≤ |2*z.im*u| := neg_le_abs _
      _ = _ := by simp only [r,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  obtain ⟨hW,hWi⟩ := spectralABLCoshHeightWeight_integral b r hb hb₁ hr hr₁
  have hbnd : ∀ᵐ u : ℝ ∂(volume : Measure ℝ),
      ‖Complex.exp (2*I*z*(u : ℂ))*spectralABLOppositeCosineProfile f u‖ ≤
        (8*M)*spectralABLCoshHeightWeight b r u := by
    refine ae_of_all _ fun u => ?_
    rw [norm_mul]
    calc
      _ ≤ Real.exp (r*|u|)*(8*M/(1+b*Real.sinh |u|)^3) :=
        mul_le_mul (hE u) (hφ u) (norm_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [spectralABLCoshHeightWeight]; ring
  rw [(spectralABLOppositeTransform_cosine f hf hc hp z hz).2,norm_mul,norm_div,norm_one,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ (1/Real.pi)*(∫ u : ℝ, (8*M)*spectralABLCoshHeightWeight b r u) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le (hW.const_mul _) hbnd) (by positivity)
    _ = ((1/Real.pi)*(8*M))*(∫ u : ℝ, spectralABLCoshHeightWeight b r u) := by
      rw [integral_const_mul]; ring
    _ ≤ ((1/Real.pi)*(8*M))*(2*(1+Real.log (4/b))*Real.exp (r*Real.log (4/b))) :=
      mul_le_mul_of_nonneg_left hWi (by positivity)
    _ = _ := by dsimp [M,r]; ring

end
end ArtinMatthews
