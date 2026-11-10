module

public import ArtinMatthews.SpectralEisensteinRadialApproximation
public import ArtinMatthews.SpectralEisensteinVerticalCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform logarithmic derivative bounds and genuine derivative convergence
for the compact radial approximants. The bound is independent of the cutoff scale. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

theorem eisensteinHeightCutoff_weighted_deriv_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t| ≤ M := by
  have hc : Continuous (fun t : ℝ => t*deriv eisensteinHeightCutoff t) :=
    continuous_id.mul (contDiff_infty_iff_deriv.mp eisensteinHeightCutoff_contDiff).2.continuous
  have hs : HasCompactSupport (fun t : ℝ => t*deriv eisensteinHeightCutoff t) := by
    apply (isCompact_Icc : IsCompact (Icc (1:ℝ) 2)).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    have ho : t < 1 ∨ 2 < t := by simpa only [mem_Icc,not_and_or,not_le] using hn
    exact ht (by simp only [eisensteinHeightCutoff_deriv_zero ho,mul_zero])
  obtain ⟨M,hM⟩ := hs.exists_bound_of_continuous hc
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro t
  have ht : |t*deriv eisensteinHeightCutoff t| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM t
  exact ht.trans (le_max_left _ _)

theorem eisensteinRadialApprox_deriv (s : ℂ) (A h : ℝ) (hh : 0 < h) :
    deriv (eisensteinRadialApprox s A) h=
      ((-deriv eisensteinHeightCutoff h*eisensteinHeightCutoff (A*h)+
        (1-eisensteinHeightCutoff h)*A*deriv eisensteinHeightCutoff (A*h):ℝ):ℂ)*(h:ℂ)^s+
      (((1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)*
        (s*(h:ℂ)^(s-1)) := by
  have hd (t : ℝ) : HasDerivAt eisensteinHeightCutoff (deriv eisensteinHeightCutoff t) t :=
    (eisensteinHeightCutoff_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc := ((hd h).const_sub 1).mul ((hd (A*h)).comp h ((hasDerivAt_id h).const_mul A))
  have he := hc.ofReal_comp.mul (eisensteinPositivePower_hasDerivAt s h hh)
  have he' : HasDerivAt (eisensteinRadialApprox s A)
      (((-deriv eisensteinHeightCutoff h*eisensteinHeightCutoff (A*h)+
        (1-eisensteinHeightCutoff h)*A*deriv eisensteinHeightCutoff (A*h):ℝ):ℂ)*(h:ℂ)^s+
      (((1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)*(s*(h:ℂ)^(s-1))) h := by
    convert he using 1
    · rfl
    · simp only [Pi.mul_apply,Function.comp_apply,mul_one]
      push_cast
      ring
  exact he'.deriv

theorem eisensteinRadialApprox_weighted_deriv (s : ℂ) (A h : ℝ) (hh : 0 < h) :
    (h:ℂ)*deriv (eisensteinRadialApprox s A) h=
      (-(((h*deriv eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)+
        (((1-eisensteinHeightCutoff h)*((A*h)*deriv eisensteinHeightCutoff (A*h)):ℝ):ℂ)+
        s*(((1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ))*(h:ℂ)^s := by
  rw [eisensteinRadialApprox_deriv s A h hh,
    Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hh.ne'),Complex.cpow_one]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hh.ne']

theorem eisensteinRadialApprox_weighted_deriv_le (s : ℂ) (A h M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t| ≤ M)
    (hh : 0 < h) :
    ‖(h:ℂ)*deriv (eisensteinRadialApprox s A) h‖ ≤ (2*M+‖s‖)*h^s.re := by
  have hχ (t : ℝ) : |eisensteinHeightCutoff t| ≤ 1 := by
    rw [abs_of_nonneg (eisensteinHeightCutoff_range t).1]
    exact (eisensteinHeightCutoff_range t).2
  have hη : |1-eisensteinHeightCutoff h| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (eisensteinHeightCutoff_range h).2)]
    linarith [(eisensteinHeightCutoff_range h).1]
  have h1 : ‖(((h*deriv eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)‖ ≤ M := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ M*1 := mul_le_mul (hbound h) (hχ _) (abs_nonneg _) hM
      _=M := mul_one _
  have h2 : ‖(((1-eisensteinHeightCutoff h)*((A*h)*deriv eisensteinHeightCutoff (A*h)):ℝ):ℂ)‖ ≤ M := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ 1*M := mul_le_mul hη (hbound _) (abs_nonneg _) zero_le_one
      _=M := one_mul _
  have h3 : ‖s*(((1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)‖ ≤ ‖s‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ ‖s‖*(1*1) := mul_le_mul_of_nonneg_left
        (mul_le_mul hη (hχ _) (abs_nonneg _) zero_le_one) (norm_nonneg _)
      _=‖s‖ := by ring
  rw [eisensteinRadialApprox_weighted_deriv s A h hh,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hh]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh.le _)
  calc
    _ ≤ ‖-(((h*deriv eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)‖+
        ‖(((1-eisensteinHeightCutoff h)*((A*h)*deriv eisensteinHeightCutoff (A*h)):ℝ):ℂ)‖+
        ‖s*(((1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ):ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2*M+‖s‖ := by rw [norm_neg];linarith

theorem eisensteinRadialApprox_eventually_germ (s : ℂ) {h : ℝ} (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop, eisensteinRadialApprox s (n+1:ℕ) =ᶠ[𝓝 h] eisensteinRemainderProfile s := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2/h)
  filter_upwards [eventually_ge_atTop k] with n hn
  apply eisensteinRadialApprox_eventually_profile s
  have hnR : (k:ℝ) ≤ n := by exact_mod_cast hn
  have he := (div_lt_iff₀ hh).mp hk
  push_cast
  nlinarith

theorem eisensteinRadialApprox_deriv_tendsto (s : ℂ) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n : ℕ => deriv (eisensteinRadialApprox s (n+1:ℕ)) h) atTop
      (𝓝 (deriv (eisensteinRemainderProfile s) h)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eisensteinRadialApprox_eventually_germ s hh] with n hn
  exact hn.deriv_eq.symm

end ArtinMatthews
