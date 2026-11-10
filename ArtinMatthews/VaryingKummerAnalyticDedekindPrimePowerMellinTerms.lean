module

public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerSeries
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingLocal
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Literal prime-ideal norms, vertical majorants, and termwise smooth
Mellin inversion for the actual Dedekind prime-power series. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section

open NumberField OAI.PrimeDegreePackets MeasureTheory Set
open scoped NumberField ContDiff

variable (K : Type*) [Field K] [NumberField K]

def dedekindPrimePowerNorm (i : DedekindPrimePowerIndex K) : ℕ :=
  Ideal.absNorm i.2.1.val ^ (i.2.2+1)

theorem dedekindPrimePowerNorm_pos (i : DedekindPrimePowerIndex K) :
    0 < dedekindPrimePowerNorm K i := by
  have hN := idealsOverPrime_norm_two_le K i.2.1.property
  exact pow_pos (by omega) _

theorem dedekindPrimePowerTerm_eq_cpow (i : DedekindPrimePowerIndex K) (s : ℂ) :
    dedekindPrimePowerTerm K i s =
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*(dedekindPrimePowerNorm K i : ℂ)^(-s) := by
  simp only [dedekindPrimePowerTerm, primePowerMangoldtTerm, dedekindPrimePowerNorm, Nat.cast_pow]
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

theorem mellinPower_norm_vertical {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    ‖(x : ℂ)^((σ : ℂ)+t*Complex.I)‖ = x^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem dedekindPrimePowerTerm_norm_vertical (i : DedekindPrimePowerIndex K) (σ t : ℝ) :
    ‖dedekindPrimePowerTerm K i ((σ : ℂ)+t*Complex.I)‖ =
      ‖dedekindPrimePowerTerm K i (σ : ℂ)‖ := by
  unfold dedekindPrimePowerTerm
  rw [primePowerMangoldtTerm_norm_eq_real (idealsOverPrime_norm_two_le K i.2.1.property),
    primePowerMangoldtTerm_norm_eq_real (idealsOverPrime_norm_two_le K i.2.1.property)]
  simp

def dedekindPrimePowerMellinIntegrand (f : ℝ → ℂ) (x σ : ℝ)
    (i : DedekindPrimePowerIndex K) (t : ℝ) : ℂ :=
  (x : ℂ)^((σ : ℂ)+t*Complex.I)*dedekindPrimePowerTerm K i ((σ : ℂ)+t*Complex.I)*
    mellin f ((σ : ℂ)+t*Complex.I)

theorem dedekindPrimePowerMellinIntegrand_norm (f : ℝ → ℂ) {x : ℝ}
    (hx : 0 < x) (σ : ℝ) (i : DedekindPrimePowerIndex K) (t : ℝ) :
    ‖dedekindPrimePowerMellinIntegrand K f x σ i t‖ =
      x^σ*‖dedekindPrimePowerTerm K i (σ : ℂ)‖*‖mellin f ((σ : ℂ)+t*Complex.I)‖ := by
  simp only [dedekindPrimePowerMellinIntegrand, norm_mul, mellinPower_norm_vertical hx,
    dedekindPrimePowerTerm_norm_vertical]

theorem dedekindPrimePowerMellinIntegrand_continuous
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hcontinuous : Continuous f) {x : ℝ} (hx : 0 < x) (σ : ℝ)
    (i : DedekindPrimePowerIndex K) :
    Continuous (dedekindPrimePowerMellinIntegrand K f x σ i) := by
  have hline : Continuous (fun t : ℝ => (σ : ℂ)+t*Complex.I) := by fun_prop
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hN0 : (Ideal.absNorm i.2.1.val : ℂ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm i.2.1.val ≠ 0 by
      have hN := idealsOverPrime_norm_two_le K i.2.1.property
      omega)
  unfold dedekindPrimePowerMellinIntegrand dedekindPrimePowerTerm primePowerMangoldtTerm
  exact ((hline.const_cpow (Or.inl hx0)).mul
    (continuous_const.mul ((hline.neg.const_cpow (Or.inl hN0)).pow _))).mul
    ((smoothMellin_entire f hcompact hpositive hcontinuous).continuous.comp hline)

theorem dedekindPrimePowerMellinTerm_eq_integral
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x : ℝ} (hx : 0 < x) (σ : ℝ)
    (i : DedekindPrimePowerIndex K) :
    (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x) =
      ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, dedekindPrimePowerMellinIntegrand K f x σ i t) := by
  have hy : (0 : ℝ) < dedekindPrimePowerNorm K i := by
    exact_mod_cast dedekindPrimePowerNorm_pos K i
  have hInv := smoothMellin_inversion_integral f hcompact hpositive hsmooth σ (div_pos hy hx)
  rw [← hInv]
  calc
    _ = ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
        (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*
          (((dedekindPrimePowerNorm K i : ℝ)/x : ℝ) : ℂ)^(-((σ : ℂ)+t*Complex.I))*
            mellin f ((σ : ℂ)+t*Complex.I)) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [dedekindPrimePowerMellinIntegrand, dedekindPrimePowerTerm_eq_cpow,
        Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hy.le hx.le,
        Complex.cpow_neg (x : ℂ), div_inv_eq_mul, Complex.ofReal_natCast]
      ring

end
end ArtinMatthews.VaryingKummerAnalytic
