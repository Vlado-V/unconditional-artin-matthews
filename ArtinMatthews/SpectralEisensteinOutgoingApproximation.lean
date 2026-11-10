module

public import ArtinMatthews.SpectralEisensteinVerticalCutoff
public import ArtinMatthews.SpectralCuspSeparableSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Genuine compact upper-height approximants to the outgoing cutoff, with
one fixed positive envelope for their mass and weighted derivatives. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

def eisensteinOutgoingApprox (q : ℂ) (A t : ℝ) : ℂ :=
  ((eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ)*(t:ℂ)^q

theorem eisensteinOutgoingApprox_smooth (q : ℂ) (A : ℝ) :
    ContDiff ℝ ∞ (eisensteinOutgoingApprox q A) := by
  have he : eisensteinOutgoingApprox q A=
      fun t => eisensteinVerticalCutoffMode q t*((1-eisensteinHeightCutoff (A*t):ℝ):ℂ) := by
    funext t
    simp only [eisensteinOutgoingApprox,eisensteinVerticalCutoffMode,Complex.ofReal_mul]
    ring
  rw [he]
  exact (eisensteinVerticalCutoffMode_smooth q).mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.sub (eisensteinHeightCutoff_contDiff.comp (contDiff_const.mul contDiff_id))))

theorem eisensteinOutgoingApprox_zero_low (q : ℂ) (A : ℝ) {t : ℝ} (ht : t≤1) :
    eisensteinOutgoingApprox q A t=0 := by
  simp [eisensteinOutgoingApprox,eisensteinHeightCutoff_zero ht]

theorem eisensteinOutgoingApprox_zero_high (q : ℂ) {A t : ℝ} (hA : 0<A) (ht : 2/A≤t) :
    eisensteinOutgoingApprox q A t=0 := by
  have h : 2≤A*t := by simpa only [mul_comm] using (div_le_iff₀ hA).mp ht
  simp [eisensteinOutgoingApprox,eisensteinHeightCutoff_one h]

theorem eisensteinOutgoingApprox_support (q : ℂ) {A : ℝ} (hA : 0<A) :
    tsupport (eisensteinOutgoingApprox q A) ⊆ Icc 1 (2/A) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have ho : t<1 ∨ 2/A<t := by simpa only [mem_Icc,not_and_or,not_le] using hn
  exact ht (ho.elim (fun h => eisensteinOutgoingApprox_zero_low q A h.le)
    (fun h => eisensteinOutgoingApprox_zero_high q hA h.le))

theorem eisensteinOutgoingApprox_compact (q : ℂ) {A : ℝ} (hA : 0<A) :
    HasCompactSupport (eisensteinOutgoingApprox q A) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (eisensteinOutgoingApprox_support q hA)

theorem eisensteinOutgoingApprox_positive_support (q : ℂ) {A : ℝ} (hA : 0<A) :
    tsupport (eisensteinOutgoingApprox q A) ⊆ Ioi (0:ℝ) :=
  fun _ ht => zero_lt_one.trans_le (eisensteinOutgoingApprox_support q hA ht).1

theorem eisensteinOutgoingApprox_eventually_germ (q : ℂ) (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, eisensteinOutgoingApprox q (((n+1:ℕ):ℝ)⁻¹)
      =ᶠ[𝓝 t] eisensteinVerticalCutoffMode q := by
  obtain ⟨k,hk⟩ := exists_nat_ge (t+1)
  filter_upwards [eventually_ge_atTop k] with n hn
  filter_upwards [eventually_lt_nhds (by linarith : t<t+1)] with x hx
  have hN : (0:ℝ)<(n+1:ℕ) := by positivity
  have hkn : (k:ℝ)≤(n+1:ℕ) := by exact_mod_cast hn.trans (Nat.le_succ n)
  have hxN := hx.le.trans (hk.trans hkn)
  have h : (((n+1:ℕ):ℝ)⁻¹)*x≤1 := by
    simpa only [div_eq_mul_inv,mul_comm] using (div_le_one hN).mpr hxN
  simp only [eisensteinOutgoingApprox,eisensteinVerticalCutoffMode,eisensteinHeightCutoff_zero h,
    sub_zero,mul_one]

def eisensteinOutgoingEnvelopeProfile (q : ℂ) (t : ℝ) : ℝ :=
  (eisensteinHeightCutoff t+|t*deriv eisensteinHeightCutoff t|)*‖(t:ℂ)^q‖

theorem eisensteinOutgoingEnvelopeProfile_nonneg (q : ℂ) (t : ℝ) :
    0≤eisensteinOutgoingEnvelopeProfile q t :=
  mul_nonneg (add_nonneg (eisensteinHeightCutoff_range t).1 (abs_nonneg _)) (norm_nonneg _)

theorem eisensteinOutgoingEnvelopeProfile_zero (q : ℂ) {t : ℝ} (ht : t≤1) :
    eisensteinOutgoingEnvelopeProfile q t=0 := by
  have hd := spectral_deriv_zero_on_left (eisensteinHeightCutoff_contDiff.continuous_deriv (by simp))
    1 (fun _ hs => eisensteinHeightCutoff_zero hs) t ht
  simp only [eisensteinOutgoingEnvelopeProfile,eisensteinHeightCutoff_zero ht,hd,mul_zero,
    abs_zero,add_zero,zero_mul]

theorem eisensteinOutgoingEnvelopeProfile_high (q : ℂ) {t : ℝ} (ht : 2<t) :
    eisensteinOutgoingEnvelopeProfile q t=‖(t:ℂ)^q‖ := by
  simp only [eisensteinOutgoingEnvelopeProfile,eisensteinHeightCutoff_one ht.le,
    eisensteinHeightCutoff_deriv_zero (Or.inr ht),mul_zero,abs_zero,add_zero,one_mul]

theorem eisensteinOutgoingEnvelopeProfile_continuous (q : ℂ) :
    Continuous (eisensteinOutgoingEnvelopeProfile q) := by
  have hχ : Continuous (fun t : ℝ => eisensteinHeightCutoff t+|t*deriv eisensteinHeightCutoff t|) :=
    eisensteinHeightCutoff_contDiff.continuous.add
      ((continuous_id.mul (eisensteinHeightCutoff_contDiff.continuous_deriv (by simp))).abs)
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : 0<t
  · exact hχ.continuousAt.mul (eisensteinPositivePower_hasDerivAt q t ht).continuousAt.norm
  · have he : eisensteinOutgoingEnvelopeProfile q =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds (by linarith : t<1)] with u hu
      exact eisensteinOutgoingEnvelopeProfile_zero q hu.le
    exact continuousAt_const.congr he.symm

theorem eisensteinOutgoingApprox_norm_le_envelope (q : ℂ) (A t : ℝ) :
    ‖eisensteinOutgoingApprox q A t‖≤eisensteinOutgoingEnvelopeProfile q t := by
  have hχ := (eisensteinHeightCutoff_range t).1
  have hη := sub_nonneg.mpr (eisensteinHeightCutoff_range (A*t)).2
  rw [eisensteinOutgoingApprox,eisensteinOutgoingEnvelopeProfile,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hχ hη)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (mul_le_of_le_one_right hχ (sub_le_self _ (eisensteinHeightCutoff_range (A*t)).1)).trans
    (le_add_of_nonneg_right (abs_nonneg _))

end ArtinMatthews
