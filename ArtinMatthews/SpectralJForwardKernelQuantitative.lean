module

public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralBesselJAllX
public import ArtinMatthews.SpectralBesselJOrderJoint
public import ArtinMatthews.SpectralJForwardStripKernel
public import ArtinMatthews.SpectralJOrderFactoredBound
public import ArtinMatthews.SpectralWeylGaussianJImaginary
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

/-! Bounds for the actual forward J kernel at the real spectral edge,
along the real ray, and on the complementary interval. -/
namespace ArtinMatthews
open Complex Set
noncomputable section

private theorem spectral_besselJ_order_difference_bounded (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x a : ℝ) (ν₁ ν₂ : ℂ), 0 < x → x ≤ B →
      0 ≤ a → a ≤ 1/2 → ‖ν₁‖ ≤ 2 → ‖ν₂‖ ≤ 2 →
      |ν₁.re| ≤ a → |ν₂.re| ≤ a →
      ‖Complex.besselJ ν₁ (x : ℂ) - Complex.besselJ ν₂ (x : ℂ)‖ ≤
        C*x^(-a)*(1+|Real.log x|)*‖ν₁-ν₂‖ := by
  obtain ⟨D,hD,hbound⟩ := spectral_besselJ_order_deriv_norm_le_bounded B
  let M := max 1 B
  refine ⟨D*M, mul_pos hD (zero_lt_one.trans_le (le_max_left _ _)), ?_⟩
  intro x a ν₁ ν₂ hx hxB ha ha₂ hn₁ hn₂ hr₁ hr₂
  let S : Set ℂ := (Complex.reCLM.toLinearMap ⁻¹' Icc (-a) a) ∩ Metric.closedBall 0 2
  have hS : Convex ℝ S := ((convex_Icc (-a) a).linear_preimage Complex.reCLM.toLinearMap).inter
    (convex_closedBall 0 2)
  have hmem (ν : ℂ) (hn : ‖ν‖ ≤ 2) (hr : |ν.re| ≤ a) : ν ∈ S :=
    ⟨abs_le.mp hr, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn⟩
  have hd (ν : ℂ) (hν : ν ∈ S) :
      ‖deriv (fun w : ℂ => Complex.besselJ w (x : ℂ)) ν‖ ≤
        D*M*x^(-a)*(1+|Real.log x|) := by
    have hn : ‖ν‖ ≤ 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hν.2
    have hr : -a ≤ ν.re ∧ ν.re ≤ a := hν.1
    have hp : 0 ≤ ν.re+a := by linarith
    have hp' : ν.re+a ≤ 1 := by linarith
    have hM : 1 ≤ M := le_max_left _ _
    have hxM : x ≤ M := hxB.trans (le_max_right _ _)
    have hpower : x^ν.re ≤ x^(-a)*M := by
      rw [show ν.re = -a+(ν.re+a) by ring, Real.rpow_add hx]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
      calc
        _ ≤ M^(ν.re+a) := Real.rpow_le_rpow hx.le hxM hp
        _ ≤ _ := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM hp'
    calc
      _ ≤ D*x^ν.re*(1+|Real.log x|) := hbound x ν hx hxB hn (by linarith [hr.1])
      _ ≤ D*(x^(-a)*M)*(1+|Real.log x|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hD.le) (by positivity)
      _ = _ := by ring
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun ν _ => spectral_besselJ_order_differentiable hx ν) hd hS
    (hmem ν₂ hn₂ hr₂) (hmem ν₁ hn₁ hr₁)

private theorem spectralJForwardKernel_real_denominator (t : ℝ) (ht : 0 ≤ t) :
    ‖2*Complex.sin ((Real.pi : ℂ)*I*(t : ℂ))‖ = 2*Real.sinh (Real.pi*t) := by
  rw [show (Real.pi : ℂ)*I*(t : ℂ) = (Real.pi : ℂ)*((t : ℂ)*I) by ring,
    spectral_sin_pi_imaginary, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le ht))]
  norm_num

private theorem spectralJForwardKernel_zero_bound (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → x ≤ B →
      ‖spectralJForwardKernel 0 x‖ ≤ C*(1+|Real.log x|) := by
  obtain ⟨C,hC,h⟩ := spectral_besselJ_order_deriv_norm_le_bounded B
  refine ⟨C,hC,?_⟩
  intro x hx hxB
  have hd := h x 0 hx hxB (by simp) (by norm_num)
  simp only [Complex.zero_re, Real.rpow_zero, mul_one] at hd
  rw [spectralJForwardKernel_zero, norm_mul, norm_neg, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  norm_num
  calc
    _ ≤ 1 * ‖deriv (fun ν : ℂ => Complex.besselJ ν (x : ℂ)) 0‖ :=
      mul_le_mul_of_nonneg_right
        ((div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hd

private theorem spectralJForwardKernel_real_small_positive (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, 0 < t → t ≤ 1 → 0 < x → x ≤ B →
      ‖spectralJForwardKernel (t : ℂ) x‖ ≤ C*(1+|Real.log x|) := by
  obtain ⟨C,hC,hbound⟩ := spectral_besselJ_order_difference_bounded B
  refine ⟨C,hC,?_⟩
  intro t x ht ht₁ hx hxB
  let ν₁ : ℂ := -2*I*(t : ℂ)
  let ν₂ : ℂ := 2*I*(t : ℂ)
  have hnorm₁ : ‖ν₁‖ = 2*t := by
    simp [ν₁, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hnorm₂ : ‖ν₂‖ = 2*t := by
    simp [ν₂, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hre₁ : |ν₁.re| ≤ 0 := by norm_num [ν₁, Complex.mul_re, Complex.mul_im]
  have hre₂ : |ν₂.re| ≤ 0 := by norm_num [ν₂, Complex.mul_re, Complex.mul_im]
  have hdiff : ‖ν₁-ν₂‖ = 4*t := by
    rw [show ν₁-ν₂ = -4*I*(t : ℂ) by dsimp [ν₁,ν₂]; ring]
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hJ := hbound x 0 ν₁ ν₂ hx hxB (by norm_num) (by norm_num)
    (by rw [hnorm₁]; linarith) (by rw [hnorm₂]; linarith) hre₁ hre₂
  simp only [neg_zero, Real.rpow_zero, mul_one, hdiff] at hJ
  have hD : 4*t ≤ 2*Real.sinh (Real.pi*t) := by
    have hpi : 2*t ≤ Real.pi*t :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) ht.le
    have hs := Real.self_le_sinh_iff.mpr (mul_nonneg Real.pi_pos.le ht.le)
    linarith
  have hpos : 0 < 2*Real.sinh (Real.pi*t) :=
    mul_pos two_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))
  rw [spectralJForwardKernel_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), norm_div,
    spectralJForwardKernel_real_denominator t ht.le]
  exact (div_le_iff₀ hpos).mpr (hJ.trans (mul_le_mul_of_nonneg_left hD (by positivity)))

theorem spectralJForwardKernel_real_small_bound (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, |t| ≤ 1 → 0 < x → x ≤ B →
      ‖spectralJForwardKernel (t : ℂ) x‖ ≤ C*(1+|Real.log x|) := by
  obtain ⟨C₀,hC₀,hzero⟩ := spectralJForwardKernel_zero_bound B
  obtain ⟨C₁,hC₁,hsmall⟩ := spectralJForwardKernel_real_small_positive B
  refine ⟨max C₀ C₁, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro t x ht hx hxB
  have hnonneg : 0 ≤ 1+|Real.log x| := by positivity
  have hpositive (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) :
      ‖spectralJForwardKernel (r : ℂ) x‖ ≤ max C₀ C₁*(1+|Real.log x|) :=
    (hsmall r x hr hr₁ hx hxB).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg)
  rcases lt_trichotomy t 0 with ht₀|rfl|ht₀
  · have he := spectralJForwardKernel_even x (t : ℂ)
    change spectralJForwardKernel (-(t : ℂ)) x = spectralJForwardKernel (t : ℂ) x at he
    rw [← he, ← Complex.ofReal_neg]
    exact hpositive (-t) (neg_pos.mpr ht₀) (by rwa [abs_of_neg ht₀] at ht)
  · simpa only [Complex.ofReal_zero] using
      (hzero x hx hxB).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)
  · exact hpositive t ht₀ (by rwa [abs_of_pos ht₀] at ht)

theorem spectralJForwardKernel_real_large_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, 1 ≤ |t| → 0 < x →
      ‖spectralJForwardKernel (t : ℂ) x‖ ≤ C := by
  obtain ⟨D,hD,hJ⟩ := spectral_besselJ_vertical_allX 0 (by norm_num)
  refine ⟨4*D, by positivity, ?_⟩
  intro t x ht hx
  have hz : (t : ℂ) ≠ 0 := by
    intro he
    have hzero : t = 0 := Complex.ofReal_eq_zero.mp he
    simp only [hzero, abs_zero] at ht
    linarith
  have hJ₁ : ‖Complex.besselJ (-2*I*(t : ℂ)) (x : ℂ)‖ ≤ D*Real.exp (Real.pi*|t|) := by
    have he : (0 : ℂ)+2*((-t : ℝ) : ℂ)*I = -2*I*(t : ℂ) := by push_cast; ring
    simpa only [Complex.ofReal_zero, he, abs_neg, Real.rpow_zero, mul_one] using hJ (-t) x hx
  have hJ₂ : ‖Complex.besselJ (2*I*(t : ℂ)) (x : ℂ)‖ ≤ D*Real.exp (Real.pi*|t|) := by
    have he : (0 : ℂ)+2*(t : ℂ)*I = 2*I*(t : ℂ) := by ring
    simpa only [Complex.ofReal_zero, he, Real.rpow_zero, mul_one] using hJ t x hx
  have hden := spectralJForwardKernel_denominator_lower
    (z := (t : ℂ)) (by simpa only [Complex.ofReal_re] using ht)
  have hden₀ : 0 < ‖2*Complex.sin ((Real.pi : ℂ)*I*(t : ℂ))‖ :=
    (half_pos (Real.exp_pos _)).trans_le hden
  rw [spectralJForwardKernel_of_ne_zero hz, norm_div]
  apply (div_le_iff₀ hden₀).mpr
  calc
    _ ≤ D*Real.exp (Real.pi*|t|)+D*Real.exp (Real.pi*|t|) :=
      (norm_sub_le _ _).trans (add_le_add hJ₁ hJ₂)
    _ = (4*D)*(Real.exp (Real.pi*|t|)/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

private theorem spectralJForwardKernel_exceptional_positive (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ κ x : ℝ, 0 < κ → κ ≤ 1/4 → 0 < x → x ≤ B →
      ‖spectralJForwardKernel ((κ : ℂ)*I) x‖ ≤ C*x^(-2*κ)*(1+|Real.log x|) := by
  obtain ⟨C,hC,hbound⟩ := spectral_besselJ_order_difference_bounded B
  refine ⟨C,hC,?_⟩
  intro κ x hκ hκ₁ hx hxB
  let ν₁ : ℂ := ((2*κ : ℝ) : ℂ)
  let ν₂ : ℂ := ((-2*κ : ℝ) : ℂ)
  have hnorm₁ : ‖ν₁‖ = 2*κ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hnorm₂ : ‖ν₂‖ = 2*κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hre₁ : |ν₁.re| ≤ 2*κ := by
    simp [ν₁, abs_of_nonneg (show 0 ≤ 2*κ by positivity)]
  have hre₂ : |ν₂.re| ≤ 2*κ := by
    simp only [ν₂, Complex.ofReal_re, abs_of_nonpos (show -2*κ ≤ 0 by linarith)]
    linarith
  have hdiff : ‖ν₁-ν₂‖ = 4*κ := by
    rw [show ν₁-ν₂ = ((4*κ : ℝ) : ℂ) by dsimp [ν₁,ν₂]; push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hJ := hbound x (2*κ) ν₁ ν₂ hx hxB (by positivity) (by linarith)
    (by rw [hnorm₁]; linarith) (by rw [hnorm₂]; linarith) hre₁ hre₂
  have hs := Real.le_sin_mul (x := 2*κ) (by positivity) (by linarith)
  rw [show Real.pi/2*(2*κ) = Real.pi*κ by ring] at hs
  have hden : ‖2*Complex.sin ((Real.pi : ℂ)*I*((κ : ℂ)*I))‖ = 2*Real.sin (Real.pi*κ) := by
    rw [show (Real.pi : ℂ)*I*((κ : ℂ)*I) = -((Real.pi*κ : ℝ) : ℂ) by
      push_cast
      calc
        _ = (Real.pi : ℂ)*(κ : ℂ)*(I*I) := by ring
        _ = _ := by rw [I_mul_I]; ring,
      Complex.sin_neg, norm_mul, norm_neg, ← Complex.ofReal_sin, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    norm_num
  have hpos : 0 < 2*Real.sin (Real.pi*κ) := by linarith
  have hz : (κ : ℂ)*I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne') I_ne_zero
  have h₁ : -2*I*((κ : ℂ)*I) = ν₁ := by
    dsimp [ν₁]
    push_cast
    rw [show -2*I*((κ : ℂ)*I) = -2*(κ : ℂ)*(I*I) by ring, I_mul_I]
    ring
  have h₂ : 2*I*((κ : ℂ)*I) = ν₂ := by
    dsimp [ν₂]
    push_cast
    rw [show 2*I*((κ : ℂ)*I) = 2*(κ : ℂ)*(I*I) by ring, I_mul_I]
    ring
  rw [spectralJForwardKernel_of_ne_zero hz, h₁, h₂, norm_div, hden]
  apply (div_le_iff₀ hpos).mpr
  rw [hdiff, show -(2*κ) = -2*κ by ring] at hJ
  exact hJ.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

theorem spectralJForwardKernel_exceptional_bound (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ κ x : ℝ, 0 ≤ κ → κ ≤ 1/4 → 0 < x → x ≤ B →
      ‖spectralJForwardKernel ((κ : ℂ)*I) x‖ ≤ C*x^(-2*κ)*(1+|Real.log x|) := by
  obtain ⟨C₀,hC₀,hzero⟩ := spectralJForwardKernel_zero_bound B
  obtain ⟨C₁,hC₁,hpos⟩ := spectralJForwardKernel_exceptional_positive B
  refine ⟨max C₀ C₁, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro κ x hκ hκ₁ hx hxB
  rcases eq_or_lt_of_le hκ with h₀|h₀
  · subst κ
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, Real.rpow_zero, mul_one]
    exact (hzero x hx hxB).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (hpos κ x h₀ hκ₁ hx hxB).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx.le _)) (by positivity))

end
end ArtinMatthews
