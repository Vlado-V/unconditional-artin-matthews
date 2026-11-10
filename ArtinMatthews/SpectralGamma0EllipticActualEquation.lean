module

public import ArtinMatthews.SpectralGamma0EllipticForcing
public import ArtinMatthews.SpectralGamma0EllipticBand
public import ArtinMatthews.SpectralGamma0EllipticTests
public import ArtinMatthews.SpectralGamma0EllipticBandIdentification
public import ArtinMatthews.SpectralGamma0EllipticScalarEquation
public import ArtinMatthews.SpectralGamma0EllipticStripPairing
public import ArtinMatthews.SpectralGamma0EllipticTestRegularity
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The actual native completed Sobolev pair of the Green vector satisfies
its Euclidean distributional equation with the actual L² forcing. -/
noncomputable section
open Set MeasureTheory Filter
open OAI.Analysis.PDE.Weak
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

private theorem integral_test_mul_congr {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (t u v : X → ℝ) (ht : Function.support t ⊆ S) (he : u =ᵐ[μ.restrict S] v) :
    (∫ x, t x*u x ∂μ) = ∫ x, t x*v x ∂μ := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hS).mp he] with x hx
  by_cases ht0 : t x = 0
  · rw [ht0,zero_mul,zero_mul]
  · rw [hx (ht ht0)]

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

include hab

theorem gamma0EllipticGreen_second_weak_equation (N : ℕ) [NeZero N] {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c) (hac : a ≤ c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (f : Gamma0RegionL2 N) (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ spectralEllipticCoordinates ⁻¹'
      spectralEllipticBand (2*(N:ℝ)) c d) :
    (∫ x : Fin 2 → ℝ, spectralEllipticPositiveLaplacian χ x *
      (gamma0EllipticPair φ ha hφ r L N (gamma0WeakSolution N f)).1 x) =
      ∫ x : Fin 2 → ℝ, χ x * gamma0EllipticForcing φ ha hφ r L N f x := by
  let S := spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d
  have hS : MeasurableSet S := (spectralEllipticBand_measurable _ _ _).preimage
    spectralEllipticCoordinates.continuous.measurable
  have hstrip : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N:ℝ)) ∧ Y < x 1} :=
    fun x hx => ⟨(hs hx).1,hc.trans_le (hs hx).2.1⟩
  have hts : Function.support (fun p => χ (spectralEllipticCoordinates.symm p)) ⊆
      Ioc 0 (2*(N:ℝ)) ×ˢ Ioi Y := by
    intro p hp
    exact hstrip (subset_tsupport χ hp)
  have hls : Function.support (fun p => spectralEllipticPositiveLaplacian χ
      (spectralEllipticCoordinates.symm p)) ⊆ Ioc 0 (2*(N:ℝ)) ×ˢ Ioi Y := by
    intro p hp
    exact hstrip (spectralEllipticPositiveLaplacian_support χ
      (subset_tsupport _ hp))
  have he := gamma0Green_strip_scalar_weak_laplacian N r Y hY L χ hχ hcχ hstrip f
  change (∫ p, (p.2^2*spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p)) •
      L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0Green N f) p)
        ∂cuspStripMeasure (2*(N:ℝ)) Y) =
      ∫ p, χ (spectralEllipticCoordinates.symm p) •
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (f-gamma0Green N f) p)
          ∂cuspStripMeasure (2*(N:ℝ)) Y at he
  rw [cuspStrip_integral_height_cancel _ hY _ _ hls,
    cuspStrip_integral_compact_density _ hY _ _ hts] at he
  rw [← spectralEllipticCoordinates_integral
      (fun p => spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p) •
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0Green N f) p)),
    ← spectralEllipticCoordinates_integral
      (fun p => (p.2^(-2:ℤ)*χ (spectralEllipticCoordinates.symm p)) •
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (f-gamma0Green N f) p))] at he
  simp only [ContinuousLinearEquiv.symm_apply_apply,smul_eq_mul] at he
  have hheight (x : Fin 2 → ℝ) : (spectralEllipticCoordinates x).2 = x 1 := rfl
  simp only [hheight] at he
  have hv := gamma0EllipticMass_band_ae φ ha hab hφ r L N hY hc hplateau (gamma0Green N f)
  rw [gamma0Green_apply,gamma0EllipticMass_energy φ ha hab hφ r L N] at hv
  rw [← gamma0Green_apply] at hv
  have hu := gamma0EllipticMass_band_ae φ ha hab hφ r L N hY hc hplateau (f-gamma0Green N f)
  have hleft := integral_test_mul_congr volume hS (spectralEllipticPositiveLaplacian χ)
    _ _ ((subset_tsupport _).trans ((spectralEllipticPositiveLaplacian_support χ).trans hs)) hv
  have hright := integral_test_mul_congr volume hS (fun x : Fin 2 → ℝ => x 1^(-2:ℤ)*χ x)
    _ _ (by
      intro x hx
      apply hs
      apply subset_tsupport χ
      intro hz
      exact hx (by change x 1^(-2:ℤ)*χ x = 0; rw [hz,mul_zero])) hu
  rw [hleft]
  rw [← hright] at he
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [cutoffL2_ae (spectralEllipticInverseHeight a)
    (spectralEllipticInverseHeight_continuous ha) (spectralEllipticInverseHeight_bound ha)
    (gamma0EllipticMass φ ha hφ r L N (f-gamma0Green N f))] with x hx
  by_cases hz : χ x = 0
  · rw [hz,mul_zero,zero_mul,zero_mul]
  · have hax : a ≤ x 1 := hac.trans (hs (subset_tsupport χ hz)).2.1
    change gamma0EllipticForcing φ ha hφ r L N f x = _ at hx
    rw [hx,spectralEllipticInverseHeight_eq hax]
    simp only [smul_eq_mul,zpow_neg,zpow_ofNat]
    ring

end ArtinMatthews
