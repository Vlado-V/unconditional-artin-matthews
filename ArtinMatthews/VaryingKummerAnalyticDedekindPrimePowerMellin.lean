module

public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerMellinTerms
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishing
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Countable
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

/-! Smooth Mellin inversion of the genuine Dedekind prime-ideal powers.
The infinite sum--integral interchange uses the proved complete absolute
prime-power series and the actual smooth Mellin vertical integrability. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section

open NumberField MeasureTheory Set
open scoped NumberField ContDiff

variable (K : Type*) [Field K] [NumberField K]

instance dedekindPrimePowerIndex_countable : Countable (DedekindPrimePowerIndex K) := by
  classical
  unfold DedekindPrimePowerIndex
  infer_instance

theorem dedekindPrimePower_logDeriv_norm_vertical {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖-logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I)‖ ≤
      ∑' i : DedekindPrimePowerIndex K, ‖dedekindPrimePowerTerm K i (σ : ℂ)‖ := by
  have hs : 1 < ((σ : ℂ)+t*Complex.I).re := by simpa using hσ
  rw [← (dedekindZeta_neg_logDeriv_primePower_hasSum K hs).tsum_eq]
  apply (norm_tsum_le_tsum_norm (dedekindPrimePower_summable_norm K hs)).trans_eq
  exact tsum_congr fun i => dedekindPrimePowerTerm_norm_vertical K i σ t

theorem dedekindPrimePower_mellin_integrable
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun t : ℝ =>
      (x : ℂ)^((σ : ℂ)+t*Complex.I)*
        (-logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I))*
          mellin f ((σ : ℂ)+t*Complex.I)) := by
  have hline : Continuous (fun t : ℝ => (σ : ℂ)+t*Complex.I) := by fun_prop
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : Continuous (fun t : ℝ =>
      logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ha := (dedekindZeta_logDeriv_analyticAt_of_one_lt_re K
      (s := (σ : ℂ)+t*Complex.I) (by simpa using hσ)).continuousAt
    have h := ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ)+t*Complex.I) ha hline.continuousAt
    simpa only [logDeriv_apply, Function.comp_def] using h
  have hcoeff := (hline.const_cpow (Or.inl hx0)).mul hlog.neg
  have hcoeff_bound : ∀ᵐ t : ℝ, ‖(x : ℂ)^((σ : ℂ)+t*Complex.I)*
      (-logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I))‖ ≤
      x^σ*(∑' i : DedekindPrimePowerIndex K, ‖dedekindPrimePowerTerm K i (σ : ℂ)‖) := by
    filter_upwards [] with t
    rw [norm_mul, mellinPower_norm_vertical hx]
    exact mul_le_mul_of_nonneg_left (dedekindPrimePower_logDeriv_norm_vertical K hσ t)
      (Real.rpow_nonneg hx.le _)
  have hi : Integrable (fun t : ℝ => mellin f ((σ : ℂ)+t*Complex.I)) :=
    smoothMellin_verticalIntegrable f hcompact hpositive hsmooth σ
  exact (hi.mul_bdd hcoeff.aestronglyMeasurable hcoeff_bound).congr
    (Filter.Eventually.of_forall (fun t => mul_comm _ _))

/-- The exact smoothed prime-ideal-power Mellin identity; all analytic
convergence and sum--integral interchange are discharged. -/
theorem dedekindPrimePower_smoothed_hasSum
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    HasSum (fun i : DedekindPrimePowerIndex K =>
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x))
      (((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
        (x : ℂ)^((σ : ℂ)+t*Complex.I)*
          (-logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I))*
            mellin f ((σ : ℂ)+t*Complex.I))) := by
  classical
  let bound : DedekindPrimePowerIndex K → ℝ → ℝ := fun i t =>
    x^σ*‖dedekindPrimePowerTerm K i (σ : ℂ)‖*‖mellin f ((σ : ℂ)+t*Complex.I)‖
  have hnorm : Summable (fun i : DedekindPrimePowerIndex K =>
      ‖dedekindPrimePowerTerm K i (σ : ℂ)‖) :=
    dedekindPrimePower_summable_norm K (by simpa using hσ)
  have hmeas (i : DedekindPrimePowerIndex K) :
      AEStronglyMeasurable (dedekindPrimePowerMellinIntegrand K f x σ i) :=
    (dedekindPrimePowerMellinIntegrand_continuous K f hcompact hpositive hsmooth.continuous hx σ i).aestronglyMeasurable
  have hbound (i : DedekindPrimePowerIndex K) : ∀ᵐ t : ℝ,
      ‖dedekindPrimePowerMellinIntegrand K f x σ i t‖ ≤ bound i t := by
    filter_upwards [] with t
    exact (dedekindPrimePowerMellinIntegrand_norm K f hx σ i t).le
  have hsum : ∀ᵐ t : ℝ, Summable (fun i => bound i t) := by
    filter_upwards [] with t
    exact (hnorm.mul_left (x^σ)).mul_right ‖mellin f ((σ : ℂ)+t*Complex.I)‖
  have hi : Integrable (fun t : ℝ => mellin f ((σ : ℂ)+t*Complex.I)) :=
    smoothMellin_verticalIntegrable f hcompact hpositive hsmooth σ
  have hbound_integrable : Integrable (fun t : ℝ => ∑' i, bound i t) := by
    convert hi.norm.const_mul (x^σ*(∑' i : DedekindPrimePowerIndex K,
      ‖dedekindPrimePowerTerm K i (σ : ℂ)‖)) using 1
    funext t
    simp only [bound, tsum_mul_right, tsum_mul_left]
  have hlim : ∀ᵐ t : ℝ, HasSum
      (fun i => dedekindPrimePowerMellinIntegrand K f x σ i t)
      ((x : ℂ)^((σ : ℂ)+t*Complex.I)*
        (-logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I))*
          mellin f ((σ : ℂ)+t*Complex.I)) := by
    filter_upwards [] with t
    exact ((dedekindZeta_neg_logDeriv_primePower_hasSum K (s := (σ : ℂ)+t*Complex.I)
      (by simpa using hσ)).mul_left ((x : ℂ)^((σ : ℂ)+t*Complex.I))).mul_right
        (mellin f ((σ : ℂ)+t*Complex.I))
  have h := (hasSum_integral_of_dominated_convergence bound hmeas hbound hsum
    hbound_integrable hlim).mul_left ((1/(2*Real.pi) : ℝ) : ℂ)
  exact h.congr_fun fun i => dedekindPrimePowerMellinTerm_eq_integral K f hcompact hpositive hsmooth hx σ i

theorem dedekindPrimePower_smoothed_mellin
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∑' i : DedekindPrimePowerIndex K,
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)) =
      ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ,
        (x : ℂ)^((σ : ℂ)+t*Complex.I)*
          (-logDeriv (NumberField.dedekindZeta K) ((σ : ℂ)+t*Complex.I))*
            mellin f ((σ : ℂ)+t*Complex.I)) :=
  (dedekindPrimePower_smoothed_hasSum K f hcompact hpositive hsmooth hx hσ).tsum_eq

end
end ArtinMatthews.VaryingKummerAnalytic
