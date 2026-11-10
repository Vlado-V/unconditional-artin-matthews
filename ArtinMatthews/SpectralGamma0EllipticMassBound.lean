module

public import ArtinMatthews.SpectralGamma0EllipticCoreEnergy
public import ArtinMatthews.SpectralCoreLocalizationBounds
public import ArtinMatthews.SpectralCoreLocalizationChartCompact
public import ArtinMatthews.SpectralCoreLocalizationSmoothEnergy
public import ArtinMatthews.SpectralGamma0CuspMassBounds
public import ArtinMatthews.SpectralHyperbolicL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The localized scalar value is bounded by the actual full mass norm,
independently of the derivative norm.  This supplies actual L² right hand
sides for local elliptic equations with merely L² forcing. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem spectralEllipticScalar_integral_sq_le (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    (∫ x : Fin 2 → ℝ, ‖spectralEllipticScalar L F x‖^2) ≤ ‖L‖^2 * ∫ p, ‖F p‖^2 := by
  have hu := spectralEllipticScalar_contDiff L F (F.smooth (⊤ : ℕ∞))
  have hs := spectralEllipticScalar_compact L F hc
  have hi : Integrable (fun x : Fin 2 → ℝ => ‖spectralEllipticScalar L F x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hu.continuous.aestronglyMeasurable).mp
      (hu.continuous.memLp_of_hasCompactSupport hs)
  have hFi : Integrable (fun p : ℝ × ℝ => ‖F p‖^2) :=
    (memLp_two_iff_integrable_sq_norm F.continuous.aestronglyMeasurable).mp
      (F.continuous.memLp_of_hasCompactSupport hc)
  have hFc := (spectralEllipticCoordinates_measurePreserving.integrable_comp
    hFi.aestronglyMeasurable).mpr hFi
  calc
    _ ≤ ∫ x : Fin 2 → ℝ, ‖L‖^2 * ‖F (spectralEllipticCoordinates x)‖^2 :=
      integral_mono hi (hFc.const_mul _) (spectralEllipticScalar_sq_le L F)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact spectralEllipticCoordinates_integral (fun p => ‖F p‖^2)

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

include hab in
theorem gamma0EllipticLocalizedScalar_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      (∫ x : Fin 2 → ℝ,
        ‖spectralEllipticScalar L (gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ) x‖^2) ≤
        C*‖gamma0SmoothSeedMass N ψ‖^2 := by
  obtain ⟨M,hM,hcut⟩ := spectral_cutoff_coordinate_bound φ
  obtain ⟨C,hC,hmass⟩ := compact_chart_gamma0_cusp_mass_bound
    (spectralCoreChart_compact A a b ha)
  have hb : 0 < b := ha.trans_le hab
  refine ⟨(‖L‖^2+1)*b^2*M^2*C,by positivity,fun N _ ψ => ?_⟩
  let G := gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ
  let K : Set UpperHalfPlane := {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b}
  have hG : tsupport G ⊆ spectralPlaneRectangle A a b :=
    spectralCoreLocalization_support φ ha hφ _ _
  have hc : HasCompactSupport (G : ℝ × ℝ → ℂ) :=
    gamma0EllipticLocalizedSchwartz_compact φ ha hφ r N ψ
  have hKi : IsCompact K := spectralCoreChart_compact A a b ha
  have hband := hyperbolic_L2_band_transfer G.continuous.measurable
    (spectral_plane_normsq_integrable G.continuous hc) ha hab (spectral_rectangle_height_band hG)
  have hGc : Continuous (fun z : UpperHalfPlane => G (z.re,z.im)) :=
    G.continuous.comp (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
  have hFc := spectralSection_continuous (gamma0CuspSection N ψ r) (gamma0CuspSection_smooth N ψ r)
  have hGh : (∫ z : UpperHalfPlane, ‖G (z.re,z.im)‖^2) ≤
      M^2 * (∫ z in K, ‖gamma0CuspSection N ψ r z‖^2) := by
    calc
      _ = ∫ z in K, ‖G (z.re,z.im)‖^2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        have he : G (z.re,z.im) = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hG ht))
        simp only [he,norm_zero,zero_pow two_ne_zero]
      _ ≤ ∫ z in K, M^2*‖gamma0CuspSection N ψ r z‖^2 := by
        apply integral_mono ((hGc.norm.pow 2).continuousOn.integrableOn_compact hKi)
          (((hFc.norm.pow 2).continuousOn.integrableOn_compact hKi).const_mul _)
        intro z
        have he : G (z.re,z.im) = φ (z.re,z.im)*gamma0CuspSection N ψ r z := by
          rw [gamma0EllipticLocalizedSchwartz_apply]
          rw [show ((z.re : ℂ)+z.im*Complex.I) = (z : ℂ) from Complex.re_add_im _]
          rw [UpperHalfPlane.ofComplex_apply]
        change ‖G (z.re,z.im)‖^2 ≤ M^2*‖gamma0CuspSection N ψ r z‖^2
        rw [he,norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hcut (z.re,z.im)).1 2) (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  have hplane : (∫ p, ‖G p‖^2) ≤ b^2*(M^2*(C*‖gamma0SmoothSeedMass N ψ‖^2)) := by
    calc
      _ = b^2*((1/b^2)*(∫ p, ‖G p‖^2)) := by field_simp [ne_of_gt hb]
      _ ≤ b^2*(∫ z : UpperHalfPlane, ‖G (z.re,z.im)‖^2) :=
        mul_le_mul_of_nonneg_left hband.2.1 (sq_nonneg _)
      _ ≤ b^2*(M^2*(∫ z in K, ‖gamma0CuspSection N ψ r z‖^2)) :=
        mul_le_mul_of_nonneg_left hGh (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hmass N ψ r) (sq_nonneg _)) (sq_nonneg _)
  calc
    _ ≤ ‖L‖^2*(∫ p, ‖G p‖^2) := spectralEllipticScalar_integral_sq_le L G hc
    _ ≤ ‖L‖^2*(b^2*(M^2*(C*‖gamma0SmoothSeedMass N ψ‖^2))) :=
      mul_le_mul_of_nonneg_left hplane (sq_nonneg _)
    _ ≤ _ := by
      nlinarith [mul_nonneg (sq_nonneg b)
        (mul_nonneg (sq_nonneg M) (mul_nonneg hC.le (sq_nonneg ‖gamma0SmoothSeedMass N ψ‖)))]

end ArtinMatthews
