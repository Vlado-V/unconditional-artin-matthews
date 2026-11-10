module

public import ArtinMatthews.SpectralEisensteinHeightCutoff
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! The actual one-variable source cutoff has a compactly supported
Laplacian error. Its support is proved, not supplied as a premise. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

theorem eisensteinPositivePower_hasDerivAt (s : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (u:ℂ)^s) (s*(t:ℂ)^(s-1)) t := by
  have h := ((hasDerivAt_id (t:ℂ)).cpow_const (c := s)
    (Complex.ofReal_mem_slitPlane.mpr ht)).comp_ofReal
  simpa only [id_eq,mul_one] using h

theorem eisensteinPositivePower_second (s : ℂ) (t : ℝ) (ht : 0 < t) :
    deriv (deriv (fun u : ℝ => (u:ℂ)^s)) t=s*(s-1)*(t:ℂ)^(s-2) := by
  have he : deriv (fun u : ℝ => (u:ℂ)^s) =ᶠ[𝓝 t]
      (fun u : ℝ => s*(u:ℂ)^(s-1)) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact (eisensteinPositivePower_hasDerivAt s u hu).deriv
  rw [he.deriv_eq]
  have h := ((eisensteinPositivePower_hasDerivAt (s-1) t ht).const_mul s).deriv
  rw [show s-1-1=s-2 by ring] at h
  simpa only [mul_assoc] using h

theorem eisensteinPositivePower_eigen (s : ℂ) (t : ℝ) (ht : 0 < t) :
    -((t:ℂ)^2)*deriv (deriv (fun u : ℝ => (u:ℂ)^s)) t=s*(1-s)*(t:ℂ)^s := by
  rw [eisensteinPositivePower_second s t ht]
  have hn : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [Complex.cpow_sub s 2 hn,Complex.cpow_two]
  field_simp
  ring

def eisensteinVerticalCutoffMode (s : ℂ) (t : ℝ) : ℂ :=
  (eisensteinHeightCutoff t:ℂ)*(t:ℂ)^s

theorem eisensteinVerticalCutoffMode_zero (s : ℂ) {t : ℝ} (ht : t ≤ 1) :
    eisensteinVerticalCutoffMode s t=0 := by
  rw [eisensteinVerticalCutoffMode,eisensteinHeightCutoff_zero ht]
  simp

theorem eisensteinVerticalCutoffMode_one (s : ℂ) {t : ℝ} (ht : 2 ≤ t) :
    eisensteinVerticalCutoffMode s t=(t:ℂ)^s := by
  rw [eisensteinVerticalCutoffMode,eisensteinHeightCutoff_one ht]
  simp

theorem eisensteinVerticalCutoffMode_smooth (s : ℂ) :
    ContDiff ℝ ∞ (eisensteinVerticalCutoffMode s) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have hlog : ContDiffAt ℝ ∞ (fun u : ℝ => (Real.log u:ℂ)) t :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiffAt_log.mpr ht.ne')
    have hexp : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.exp (s*(Real.log u:ℂ))) t :=
      (contDiffAt_const.mul hlog).cexp
    have he : (fun u : ℝ => (u:ℂ)^s) =ᶠ[𝓝 t]
        (fun u : ℝ => Complex.exp (s*(Real.log u:ℂ))) := by
      filter_upwards [eventually_gt_nhds ht] with u hu
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
        ← Complex.ofReal_log hu.le,mul_comm]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp t
      eisensteinHeightCutoff_contDiff.contDiffAt).mul (hexp.congr_of_eventuallyEq he)
  · have he : eisensteinVerticalCutoffMode s =ᶠ[𝓝 t] fun _ => 0 := by
      have hlt : t < 1 := by linarith
      filter_upwards [eventually_lt_nhds hlt] with u hu
      exact eisensteinVerticalCutoffMode_zero s hu.le
    exact contDiffAt_const.congr_of_eventuallyEq he

def eisensteinVerticalCutoffError (s : ℂ) (t : ℝ) : ℂ :=
  -((t:ℂ)^2)*deriv (deriv (eisensteinVerticalCutoffMode s)) t-
    s*(1-s)*eisensteinVerticalCutoffMode s t

theorem eisensteinVerticalCutoffError_smooth (s : ℂ) :
    ContDiff ℝ ∞ (eisensteinVerticalCutoffError s) := by
  have h := eisensteinVerticalCutoffMode_smooth s
  have h1 := (contDiff_infty_iff_deriv.mp h).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  exact ((Complex.ofRealCLM.contDiff.pow 2).neg.mul h2).sub
    (contDiff_const.mul h)

theorem eisensteinVerticalCutoffError_zero (s : ℂ) {t : ℝ} (ht : t < 1 ∨ 2 < t) :
    eisensteinVerticalCutoffError s t=0 := by
  rcases ht with ht | ht
  · have he : eisensteinVerticalCutoffMode s =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ht] with u hu
      exact eisensteinVerticalCutoffMode_zero s hu.le
    have hd := he.deriv.deriv_eq
    rw [eisensteinVerticalCutoffError,hd,eisensteinVerticalCutoffMode_zero s ht.le]
    simp
  · have he : eisensteinVerticalCutoffMode s =ᶠ[𝓝 t] (fun u : ℝ => (u:ℂ)^s) := by
      filter_upwards [eventually_gt_nhds ht] with u hu
      exact eisensteinVerticalCutoffMode_one s hu.le
    rw [eisensteinVerticalCutoffError,he.deriv.deriv_eq,
      eisensteinVerticalCutoffMode_one s ht.le,eisensteinPositivePower_eigen s t (by linarith)]
    ring

theorem eisensteinVerticalCutoffError_support (s : ℂ) :
    tsupport (eisensteinVerticalCutoffError s) ⊆ Icc (1:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra h
  have ho : t < 1 ∨ 2 < t := by simpa only [mem_Icc,not_and_or,not_le] using h
  exact ht (eisensteinVerticalCutoffError_zero s ho)

theorem eisensteinVerticalCutoffError_compact (s : ℂ) :
    HasCompactSupport (eisensteinVerticalCutoffError s) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (eisensteinVerticalCutoffError_support s)

end ArtinMatthews
