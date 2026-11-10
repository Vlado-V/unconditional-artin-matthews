module

public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralCuspHeightDilation
public import ArtinMatthews.SpectralKLPhysicalCompactData
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped InnerProductSpace
noncomputable section

/-- The physical L2 pairing of profiles real on the positive half-line is their real dx/x integral. -/
theorem spectralKLPhysical_inner_real_integral (F G : ℝ → ℂ)
    (hF : MemLp F 2 spectralKLPhysicalMeasure) (hG : MemLp G 2 spectralKLPhysicalMeasure)
    (hFr : ∀ x : ℝ, 0 < x → star (F x) = F x)
    (hGr : ∀ x : ℝ, 0 < x → star (G x) = G x) :
    inner ℂ (hF.toLp F) (hG.toLp G) =
      ((∫ x in Ioi (0 : ℝ), (F x).re * (G x).re / x : ℝ) : ℂ) := by
  calc
    _ = ∫ x : ℝ, inner ℂ (F x) (G x) ∂spectralKLPhysicalMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hxF hxG
      change inner ℂ ((hF.toLp F) x) ((hG.toLp G) x) = inner ℂ (F x) (G x)
      rw [hxF, hxG]
    _ = ∫ x in Ioi (0 : ℝ), ((x⁻¹ : ℝ) : ℂ) * inner ℂ (F x) (G x) :=
      spectralKLPositiveWeightMeasure_complex_integral (fun x => x⁻¹)
        (fun x => inner ℂ (F x) (G x)) (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)
    _ = _ := by
      rw [← integral_complex_ofReal]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change ((x⁻¹ : ℝ) : ℂ) * inner ℂ (F x) (G x) =
        (((F x).re * (G x).re / x : ℝ) : ℂ)
      have hxF : ((F x).re : ℂ) = F x := Complex.conj_eq_iff_re.mp (by
        simpa only [Complex.star_def] using hFr x hx)
      have hxG : ((G x).re : ℂ) = G x := Complex.conj_eq_iff_re.mp (by
        simpa only [Complex.star_def] using hGr x hx)
      rw [← hxF, ← hxG]
      simp only [RCLike.inner_apply, Complex.conj_ofReal, Complex.ofReal_mul,
        Complex.ofReal_inv, Complex.ofReal_re, div_eq_mul_inv]
      ring

/-- Exact width cancellation followed by the real-valued complex physical L2 pairing. -/
theorem cuspFourierHeightPairing_dilation_inner (q w : ℝ) (hq : 0 < q) (hw : 0 < w)
    (F G : ℝ → ℂ)
    (hF : MemLp F 2 spectralKLPhysicalMeasure) (hG : MemLp G 2 spectralKLPhysicalMeasure)
    (hFr : ∀ x : ℝ, 0 < x → star (F x) = F x)
    (hGr : ∀ x : ℝ, 0 < x → star (G x) = G x) :
    (w : ℂ) * (cuspFourierHeightPairing
      (fun y => Real.sqrt (y / w) * (F ((q / w) * y)).re)
      (fun y => Real.sqrt (y / w) * (G ((q / w) * y)).re) : ℂ) =
        inner ℂ (hF.toLp F) (hG.toLp G) := by
  rw [spectralKLPhysical_inner_real_integral F G hF hG hFr hGr]
  exact_mod_cast cuspFourierHeightPairing_dilation q w hq hw (fun x => (F x).re) (fun x => (G x).re)

end
end ArtinMatthews
