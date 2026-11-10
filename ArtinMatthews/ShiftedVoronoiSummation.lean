module

public import ArtinMatthews.ShiftedVoronoiAdditiveContinuation
public import ArtinMatthews.ShiftedVoronoiBesselTransform
public import ArtinMatthews.ShiftedVoronoiRadialNormalization
public import ArtinMatthews.ShiftedVoronoiCuspContour
public import ArtinMatthews.ShiftedVoronoiDualSummation
public import ArtinMatthews.ShiftedVoronoiPowerNormalization
public import ArtinMatthews.ShiftedVoronoiSourceSummation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Weight-one Voronoi summation from actual cuspidal modularity

The two convergent coefficient series are connected by Mellin inversion,
the actual rational-cusp functional equation, and the Gaussian-regulated
contour theorem. The Bessel kernel and its normalization have already been
identified analytically. No Voronoi or coefficient-summation identity is an input.
-/

noncomputable section
open Complex UpperHalfPlane MeasureTheory Set Filter
open scoped MatrixGroups Topology ContDiff

namespace ArtinMatthews

/-- The functional equation with its powers collected at the actual dual scale. -/
theorem cuspAdditiveL_mellin_reflected_normalized
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (s : ℂ) (hs : s.re < 0) :
    mellin W s * cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) s =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I / (γ 1 0 : ℂ)) *
        (mellin (normalizedRadialFourier W) (1 - s) *
          ((((γ 1 0 : ℝ) ^ 2 / (2 * Real.pi) ^ 2 : ℝ)) : ℂ) ^ (1 - s) *
            LSeries (cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0)) (1 - s)) := by
  rw [cuspAdditiveL_mellin_reflected f hperiod γ hγ hq W a b ha hW s hs]
  have hp := voronoi_power_normalization (2 * Real.pi) ((γ 1 0 : ℝ) ^ 2)
    (by positivity) (sq_pos_of_ne_zero (by exact_mod_cast hq)) s
  calc
    _ = (Complex.I / (γ 1 0 : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) ^ s * (((γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s) *
          ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))) *
        LSeries (cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0)) (1 - s) *
        mellin (normalizedRadialFourier W) (1 - s) := by ring
    _ = _ := by rw [hp]; ring

/-- The weight-one Voronoi identity for a genuine cusp form and a positive
compact Schwartz test. The factor is `1/q`, and the transform is
`2πi ∫ H(x) J₀(4π√(xy)) dx`. -/
theorem weightOne_voronoi
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) :
    (∑' n : ℕ, cuspAdditiveCoeff f ((γ 0 0 : ℝ) / γ 1 0) n * W (n : ℝ)) =
      (1 / (γ 1 0 : ℂ)) * ∑' n : ℕ,
        cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0) n *
          weightOneBesselTransform W ((n : ℝ) / (γ 1 0 : ℝ) ^ 2) := by
  let Q : ℝ := (γ 1 0 : ℝ) ^ 2
  have hQ : 0 < Q := sq_pos_of_ne_zero (by exact_mod_cast hq)
  let D (t : ℝ) : ℂ := mellin (normalizedRadialFourier W) ((2 : ℂ) + t * Complex.I) *
    ((Q / (2 * Real.pi) ^ 2 : ℝ) : ℂ) ^ ((2 : ℂ) + t * Complex.I) *
      LSeries (cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0)) ((2 : ℂ) + t * Complex.I)
  have he (t : ℝ) : mellin W ((-1 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((-1 : ℂ) + t * Complex.I) =
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I / (γ 1 0 : ℂ)) * D (-t) := by
    rw [cuspAdditiveL_mellin_reflected_normalized f hperiod γ hγ hq W a b ha hW _ (by simp)]
    have hu : 1 - ((-1 : ℂ) + t * Complex.I) = (2 : ℂ) + (-t : ℝ) * Complex.I := by
      push_cast
      ring
    rw [hu]
  have hint : (∫ t : ℝ, mellin W ((-1 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((-1 : ℂ) + t * Complex.I)) =
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I / (γ 1 0 : ℂ)) * ∫ t : ℝ, D t := by
    simp_rw [he]
    rw [integral_const_mul, integral_neg_eq_self]
  have hsrc := weightOne_source_sum_mellin f hperiod ((γ 0 0 : ℝ) / γ 1 0)
    W (W.smooth ⊤) a b ha hW 2 1 (by norm_num) (by norm_num)
  simp only [div_one, Complex.ofReal_one, one_cpow, mul_one, Complex.ofReal_ofNat] at hsrc
  have hdual := weightOne_dual_sum_mellin f hperiod (-(γ 1 1 : ℝ) / γ 1 0)
    W a b ha hW 2 Q (by norm_num) hQ
  simp only [Complex.ofReal_ofNat] at hdual
  rw [hsrc.tsum_eq, hdual.tsum_eq,
    ← cuspAdditiveL_mellin_contour f hperiod γ hγ hq W a b ha hW, hint]
  change _ = (1 / (γ 1 0 : ℂ)) *
    ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, D t))
  ring

/-- Equation (5.3) for an arbitrary smooth test supported in a positive compact interval. -/
theorem weightOne_voronoi_of_smooth_compact
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) :
    (∑' n : ℕ, cuspAdditiveCoeff f ((γ 0 0 : ℝ) / γ 1 0) n * H (n : ℝ)) =
      (1 / (γ 1 0 : ℂ)) * ∑' n : ℕ,
        cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0) n *
          weightOneBesselTransform H ((n : ℝ) / (γ 1 0 : ℝ) ^ 2) := by
  have hcompact : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hHs
  let W : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hH
  exact weightOne_voronoi f hperiod γ hγ hq W a b ha hHs

end ArtinMatthews
