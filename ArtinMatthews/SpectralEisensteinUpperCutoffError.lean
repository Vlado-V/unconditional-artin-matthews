module

public import ArtinMatthews.SpectralEisensteinOutgoingApproximation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The exact upper cutoff error is a dilation of the original compact
forcing. The two cutoff bands are disjoint when the upper scale is small. -/
noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

def eisensteinUpperCutoffMode (q : ℂ) (A t : ℝ) : ℂ :=
  (A:ℂ)^(-q)*eisensteinVerticalCutoffMode q (A*t)

def eisensteinUpperCutoffError (q : ℂ) (A t : ℝ) : ℂ :=
  (A:ℂ)^(-q)*eisensteinVerticalCutoffError q (A*t)

theorem eisensteinUpperCutoffMode_smooth (q : ℂ) (A : ℝ) :
    ContDiff ℝ ∞ (eisensteinUpperCutoffMode q A) :=
  contDiff_const.mul ((eisensteinVerticalCutoffMode_smooth q).comp (contDiff_const.mul contDiff_id))

theorem eisensteinUpperCutoffError_smooth (q : ℂ) (A : ℝ) :
    ContDiff ℝ ∞ (eisensteinUpperCutoffError q A) :=
  contDiff_const.mul ((eisensteinVerticalCutoffError_smooth q).comp (contDiff_const.mul contDiff_id))

theorem eisensteinUpperCutoffError_zero (q : ℂ) {A t : ℝ}
    (ht : A*t<1 ∨ 2<A*t) : eisensteinUpperCutoffError q A t=0 := by
  rw [eisensteinUpperCutoffError,eisensteinVerticalCutoffError_zero q ht,mul_zero]

theorem eisensteinUpperCutoffError_support (q : ℂ) {A : ℝ} (hA : 0<A) :
    tsupport (eisensteinUpperCutoffError q A) ⊆ Icc (1/A) (2/A) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have ho : t<1/A ∨ 2/A<t := by simpa only [mem_Icc,not_and_or,not_le] using hn
  apply ht
  apply eisensteinUpperCutoffError_zero q
  simpa only [mul_comm A t] using
    ho.imp (lt_div_iff₀ hA).mp (div_lt_iff₀ hA).mp

theorem eisensteinUpperCutoffError_compact (q : ℂ) {A : ℝ} (hA : 0<A) :
    HasCompactSupport (eisensteinUpperCutoffError q A) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (eisensteinUpperCutoffError_support q hA)

theorem eisensteinUpperCutoffError_positive_support (q : ℂ) {A : ℝ} (hA : 0<A) :
    tsupport (eisensteinUpperCutoffError q A) ⊆ Ioi (0:ℝ) :=
  fun _ h => (one_div_pos.mpr hA).trans_le (eisensteinUpperCutoffError_support q hA h).1

theorem eisensteinUpperCutoffMode_eq (q : ℂ) {A t : ℝ} (hA : 0<A) (ht : 0<t) :
    eisensteinUpperCutoffMode q A t=(eisensteinHeightCutoff (A*t):ℂ)*(t:ℂ)^q := by
  have he : (A:ℂ)^(-q)*((A*t:ℝ):ℂ)^q=(t:ℂ)^q := by
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hA.le ht.le,← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hA.ne'),neg_add_cancel,Complex.cpow_zero,one_mul]
  rw [eisensteinUpperCutoffMode,eisensteinVerticalCutoffMode,mul_left_comm,he]

theorem eisensteinOutgoingApprox_eq_cutoffs (q : ℂ) {A : ℝ} (hA : 0<A) (hA2 : A≤1/2) :
    eisensteinOutgoingApprox q A=fun t => eisensteinVerticalCutoffMode q t-eisensteinUpperCutoffMode q A t := by
  funext t
  by_cases ht : 0<t
  · rw [eisensteinUpperCutoffMode_eq q hA ht,eisensteinVerticalCutoffMode,eisensteinOutgoingApprox]
    by_cases hAt : A*t≤1
    · rw [eisensteinHeightCutoff_zero hAt]
      simp
    · have ht2 : 2≤t := by nlinarith [mul_le_mul_of_nonneg_right hA2 ht.le]
      rw [eisensteinHeightCutoff_one ht2]
      simp only [one_mul,Complex.ofReal_sub,Complex.ofReal_one]
      ring
  · have ht1 : t≤1 := by linarith
    have hAt : A*t≤1 := (mul_nonpos_of_nonneg_of_nonpos hA.le (le_of_not_gt ht)).trans zero_le_one
    simp only [eisensteinOutgoingApprox_zero_low q A ht1,eisensteinVerticalCutoffMode_zero q ht1,
      eisensteinUpperCutoffMode,eisensteinVerticalCutoffMode_zero q hAt,mul_zero,sub_zero]

theorem spectralDeriv_rescale_const_mul (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (c : ℂ) (A t : ℝ) :
    deriv (fun u => c*f (A*u)) t=c*(A:ℂ)*deriv f (A*t) := by
  have he := ((hf (A*t)).hasDerivAt.scomp t ((hasDerivAt_id t).const_mul A)).const_mul c
  simpa only [Function.comp_apply,id_eq,mul_one,Complex.real_smul,mul_assoc] using he.deriv

theorem spectralSecondDeriv_rescale_const_mul (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (c : ℂ) (A t : ℝ) :
    deriv (deriv (fun u => c*f (A*u))) t=c*(A:ℂ)^2*deriv (deriv f) (A*t) := by
  have he : deriv (fun u => c*f (A*u))=fun u => c*(A:ℂ)*deriv f (A*u) :=
    funext (spectralDeriv_rescale_const_mul f (hf.differentiable (by simp)) c A)
  rw [he]
  exact (by
    simpa only [pow_two,mul_assoc] using spectralDeriv_rescale_const_mul (deriv f)
      ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) (c*(A:ℂ)) A t)

theorem spectralSecondDeriv_sub (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (t : ℝ) :
    deriv (deriv (fun u => f u-g u)) t=deriv (deriv f) t-deriv (deriv g) t := by
  have he : deriv (fun u => f u-g u)=fun u => deriv f u-deriv g u := by
    funext u
    exact deriv_sub ((hf.differentiable (by simp)) u) ((hg.differentiable (by simp)) u)
  rw [he]
  exact deriv_sub (((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) t)
    (((contDiff_infty_iff_deriv.mp hg).2.differentiable (by simp)) t)

theorem eisensteinOutgoingApprox_radial_error (q : ℂ) {A : ℝ} (hA : 0<A) (hA2 : A≤1/2) (t : ℝ) :
    -((t:ℂ)^2)*deriv (deriv (eisensteinOutgoingApprox q A)) t-
      q*(1-q)*eisensteinOutgoingApprox q A t =
      eisensteinVerticalCutoffError q t-eisensteinUpperCutoffError q A t := by
  rw [eisensteinOutgoingApprox_eq_cutoffs q hA hA2,
    spectralSecondDeriv_sub _ _ (eisensteinVerticalCutoffMode_smooth q) (eisensteinUpperCutoffMode_smooth q A)]
  unfold eisensteinUpperCutoffMode eisensteinUpperCutoffError eisensteinVerticalCutoffError
  rw [spectralSecondDeriv_rescale_const_mul _ (eisensteinVerticalCutoffMode_smooth q)]
  push_cast
  ring

end ArtinMatthews
