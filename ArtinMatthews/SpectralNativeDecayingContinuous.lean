module

public import ArtinMatthews.SpectralDecayingPoincare
public import ArtinMatthews.SpectralEisensteinAnalysisCompletion
public import ArtinMatthews.SpectralPrimitiveFourierAmplitude
public import ArtinMatthews.SpectralDecayingPhysicalPairing
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralNativeCompactContinuous
public import ArtinMatthews.SpectralNativeLpLimit
public import ArtinMatthews.SpectralNativeOrderCutoff
public import ArtinMatthews.SpectralTrueWidthPhysicalProfile
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

/-! The actual completed Eisenstein analysis of the native noncompact
Poincare vector is obtained from its original compact approximants. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0PrimitiveDecayingPoincare_continuous_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Z : ℝ) (hZ : 0 < Z)
    (P : SpectralDecayingHeightProfile) (i : Gamma0EisensteinCuspClasses N) :
    (gamma0EisensteinAnalysis N (gamma0PrimitiveDecayingPoincare N r n P)) i
      =ᵐ[gamma0EisensteinSpectralMeasure] fun t => star
        (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i) r Z hZ n hn
          (eisensteinCriticalPoint t)*
          ∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
            (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
              (fun y => P.value ((gamma0CuspTrueWidth N r : ℝ)*y)) x/(x : ℂ))) := by
  let q := |cuspFourierFrequency 1 n|
  let w := (gamma0CuspTrueWidth N r : ℝ)
  let f := spectralKLHeightPhysicalTest q (fun y => P.value (w*y))
  let H (K : ℕ) := gamma0PrimitiveFourierPoincareTest N r n
    (spectralHeightProfilePartial K P.value)
    (spectralHeightProfilePartial_contDiff K P.value P.smooth)
    (spectralHeightProfilePartial_compact K P.value)
    (spectralHeightProfilePartial_positive K P.value)
  let F (K : ℕ) : Lp ℂ 2 gamma0EisensteinSpectralMeasure := (gamma0EisensteinAnalysis N (H K)) i
  let Amp (t : ℝ) := gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i)
    r Z hZ n hn (eisensteinCriticalPoint t)
  let G (t : ℝ) : ℂ := star (Amp t*∫ x in Ioi (0 : ℝ),
    schlafliBesselK ((t : ℂ)*Complex.I) x*(f x/(x : ℂ)))
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hf : Measurable f := spectralKLHeightPhysicalTest_width_measurable hq hw P.value P.smooth.continuousOn
  have hp : ∀ x, 0 < x → ‖f x‖ ≤
      (P.bound*w^P.exponent/q^(P.exponent-1/2))*x^(P.exponent-1/2) :=
    fun _ hx => spectralKLHeightPhysicalTest_decaying_power hq hw P hx
  have hPb := P.bound_nonneg
  have hF : Tendsto F atTop
      (𝓝 ((gamma0EisensteinAnalysis N (gamma0PrimitiveDecayingPoincare N r n P)) i)) := by
    have hc : Continuous (fun v : Gamma0RegionL2 N => (gamma0EisensteinAnalysis N v) i) :=
      (PiLp.continuous_apply 2 _ i).comp (gamma0EisensteinAnalysis N).continuous
    exact (hc.tendsto _).comp (gamma0PrimitiveDecayingPoincare_partial_tendsto N r n P)
  have hcoeff (K : ℕ) : F K =ᵐ[gamma0EisensteinSpectralMeasure] fun t => star
      (Amp t*∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
        (spectralWeylProfileCutoff (w/q) K f x/(x : ℂ))) := by
    let Y : ℝ := ((2 : ℝ)^(K+1))⁻¹/2
    have hY : 0 < Y := by dsimp only [Y]; positivity
    have hs : tsupport (spectralHeightProfilePartial K P.value) ⊆ Ioi Y := by
      intro y hy
      have hy' := (spectralHeightProfilePartial_tsupport K P.value hy).1
      have hpos : 0 < ((2 : ℝ)^(K+1))⁻¹ := by positivity
      exact (half_lt_self hpos).trans_le hy'
    have h := gamma0PrimitiveAnalysis_fourier_ae N r n hn Z hZ Y hY
      (spectralHeightProfilePartial K P.value)
      (spectralHeightProfilePartial_contDiff K P.value P.smooth)
      (spectralHeightProfilePartial_compact K P.value)
      (spectralHeightProfilePartial_positive K P.value) hs i
    simp_rw [spectralKLHeightPhysicalTest_partial_width] at h
    exact h
  have hAll : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure, ∀ K, F K t = star
      (Amp t*∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
        (spectralWeylProfileCutoff (w/q) K f x/(x : ℂ))) := ae_all_iff.mpr hcoeff
  have hpoint : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure, Tendsto (fun K => F K t) atTop (𝓝 (G t)) := by
    filter_upwards [hAll] with t ht
    have h := (spectralKLPower_order_cutoff_tendsto f hf (div_pos hw hq)
      (by positivity : 0 ≤ P.bound*w^P.exponent/q^(P.exponent-1/2))
      (by norm_num : (0 : ℝ) ≤ 0)
      (by linarith [P.exponent_gt_one] : 0 < P.exponent-1/2) hp ((t : ℂ)*Complex.I)
      (by simp : |((t : ℂ)*Complex.I).re| ≤ 0)).const_mul (Amp t)
    apply h.star.congr'
    exact Eventually.of_forall (fun K => (ht K).symm)
  exact spectralLp_two_limit_ae F _ G hF hpoint

end ArtinMatthews
