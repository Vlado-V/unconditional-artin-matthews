module

public import ArtinMatthews.ShiftedVoronoiBesselTransform
public import ArtinMatthews.ShiftedVoronoiCoefficientSeries
public import ArtinMatthews.ShiftedVoronoiRadialNormalization
public import ArtinMatthews.ShiftedVoronoiMellinSummation
public import ArtinMatthews.ShiftedVoronoiRightHalfPlane
public import ArtinMatthews.ShiftedVoronoiSourceSummation
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# The dual Bessel-weighted coefficient sum

The same absolute sum–integral argument applies to the actual Bessel transform,
using its proved right-half-plane Mellin inversion. In particular the dual
series is proved summable, rather than interpreted as a formal series.
-/

noncomputable section
open Complex UpperHalfPlane MeasureTheory Set Filter
open scoped Topology

namespace ArtinMatthews

/-- Identifies the exact weight-one normalization with the normalized radial transform. -/
theorem weightOneBesselTransform_eq_normalized
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (y : ℝ) (hy : 0 < y) :
    weightOneBesselTransform W y = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      normalizedRadialFourier W ((2 * Real.pi) ^ 2 * y) := by
  rw [weightOneBesselTransform_gamma_inversion_right W a b ha hW 2 y (by norm_num) hy,
    normalizedRadialFourier_gamma_mellin_inversion_right W a b ha hW 2 _ (by norm_num)
      (by positivity)]
  congr 2
  ring

/-- An absolutely convergent Mellin representation of the dual Bessel sum. -/
theorem weightOne_dual_sum_mellin
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x : ℝ) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ Q : ℝ) (hσ : 1 < σ) (hQ : 0 < Q) :
    HasSum (fun n : ℕ ↦ cuspAdditiveCoeff f x n * weightOneBesselTransform W ((n : ℝ) / Q))
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        ((((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ t : ℝ,
          mellin (normalizedRadialFourier W) ((σ : ℂ) + t * Complex.I) *
            ((Q / (2 * Real.pi) ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I) *
              LSeries (cuspAdditiveCoeff f x) ((σ : ℂ) + t * Complex.I))) := by
  let Z := Q / (2 * Real.pi) ^ 2
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hi := hasSum_mellinInv_scaled (fun n : ℕ ↦ cuspAdditiveCoeff f x (n + 1))
    (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) (fun n ↦ by positivity)
    (mellin (normalizedRadialFourier W)) σ
    (normalizedRadialFourier_mellin_vertical_integrable_right W a b ha hW σ (by linarith))
    (cuspAdditiveCoeff_summable_natSucc f hperiod x σ hσ) Z hZ
  have hterms (n : ℕ) : mellinInv σ (mellin (normalizedRadialFourier W))
      (((n + 1 : ℕ) : ℝ) / Z) = normalizedRadialFourier W (((n + 1 : ℕ) : ℝ) / Z) :=
    normalizedRadialFourier_mellin_inversion_right W a b ha hW σ _ (by linarith) (by positivity)
  simp only [hterms] at hi
  have hseries (t : ℝ) : (∑' n : ℕ, cuspAdditiveCoeff f x (n + 1) *
      (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I))) =
      LSeries (cuspAdditiveCoeff f x) ((σ : ℂ) + t * Complex.I) := by
    simpa only [Complex.ofReal_natCast] using
      cuspAdditiveCoeff_tsum_natSucc f hperiod x _ (by simpa using hσ)
  simp only [hseries] at hi
  have hs := hi.mul_left (((2 * Real.pi : ℝ) : ℂ) * Complex.I)
  have hsingle (n : ℕ) : (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
      (cuspAdditiveCoeff f x (n + 1) * normalizedRadialFourier W (((n + 1 : ℕ) : ℝ) / Z)) =
      cuspAdditiveCoeff f x (n + 1) * weightOneBesselTransform W (((n + 1 : ℕ) : ℝ) / Q) := by
    rw [weightOneBesselTransform_eq_normalized W a b ha hW _ (by positivity)]
    have he : (((n + 1 : ℕ) : ℝ) / Z) =
        (2 * Real.pi) ^ 2 * (((n + 1 : ℕ) : ℝ) / Q) := by
      dsimp [Z]
      field_simp
    rw [he]
    ring
  simp only [hsingle] at hs
  have hall := (hasSum_nat_add_iff (f := fun n : ℕ ↦ cuspAdditiveCoeff f x n *
    weightOneBesselTransform W ((n : ℝ) / Q)) 1).mp hs
  simpa only [Finset.sum_range_one, cuspAdditiveCoeff_zero f hperiod x,
    zero_mul, add_zero] using hall

end ArtinMatthews
