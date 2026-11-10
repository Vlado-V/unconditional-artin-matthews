module

public import ArtinMatthews.GiantProgressionGlobalMean
public import ArtinMatthews.MarkedCorrelationNormalization
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The ordinary fixed-progression smooth prime mean in main-term plus
little-o form, including arbitrary fixed finite prime deletions. -/
namespace ArtinMatthews
open Filter
open scoped Topology Asymptotics

theorem giant_mean_error_isLittleO (F : ℝ → ℂ) (L : ℂ)
    (h : Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*F x) atTop (𝓝 L)) :
    (fun x => F x-L*((x/Real.log x : ℝ) : ℂ)) =o[atTop] (fun x : ℝ => x/Real.log x) := by
  apply marked_correlation_isLittleO_of_normalized_norm
  have hz := h.sub_const L
  simp only [sub_self] at hz
  have hn := tendsto_zero_iff_norm_tendsto_zero.mp hz
  apply hn.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x≠0 := (zero_lt_one.trans hx).ne'
  have hl : Real.log x≠0 := (Real.log_pos hx).ne'
  have hi : ((Real.log x/x : ℝ) : ℂ)*((x/Real.log x : ℝ) : ℂ) = 1 := by
    norm_cast
    field_simp [hx0,hl]
  have he : ((Real.log x/x : ℝ) : ℂ)*(F x-L*((x/Real.log x : ℝ) : ℂ)) =
      ((Real.log x/x : ℝ) : ℂ)*F x-L := by
    calc
      _ = ((Real.log x/x : ℝ) : ℂ)*F x - L*
          (((Real.log x/x : ℝ) : ℂ)*((x/Real.log x : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hi,mul_one]
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.log_pos hx).le (by linarith))]

theorem giant_shifted_prime_series_asymptotic {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hc : HasCompactSupport Φ)
    (hp : tsupport Φ ⊆ Set.Ioi 0) :
    (fun x => giantShiftedPrimeSeries U Φ x -
      (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)*((x/Real.log x : ℝ) : ℂ))
      =o[atTop] (fun x : ℝ => x/Real.log x) :=
  giant_mean_error_isLittleO _ _ (giant_shifted_prime_series_mean U Φ hΦ hderiv hc hp)

theorem giant_shifted_prime_series_deleted_asymptotic {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (E : Finset ℕ) (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hc : HasCompactSupport Φ)
    (hp : tsupport Φ ⊆ Set.Ioi 0) :
    (fun x => giantShiftedPrimeSeriesDeleted U E Φ x -
      (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)*((x/Real.log x : ℝ) : ℂ))
      =o[atTop] (fun x : ℝ => x/Real.log x) :=
  giant_mean_error_isLittleO _ _ (giant_shifted_prime_series_mean_delete_fixed U E Φ hΦ hderiv hc hp)

end ArtinMatthews
