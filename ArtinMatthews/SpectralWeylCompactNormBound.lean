module

public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import ArtinMatthews.SpectralWeylPhysicalBilinearGaussian
public import ArtinMatthews.SpectralWeylPlanarCoordinates
public import ArtinMatthews.SpectralKLMacdonaldSpectralFubini
public import ArtinMatthews.SpectralWeylOrbitalFrequency
public import ArtinMatthews.SpectralWeylPhysicalContinuity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! An actual height-explicit absolute orbital bound. The checked fold
turns both compact lower-height supports into a uniform kernel bound,
with no frequency dependence absorbed into the constants. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralWeylPhysicalBilinear_compact_norm_bound {X a b M : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hb : 0 < b) (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hflo : ∀ z ∈ tsupport f, a ≤ z) (hglo : ∀ z ∈ tsupport g, b ≤ z)
    (hM : ∀ z : ℝ, ‖f z‖ ≤ M) :
    ‖spectralWeylPhysicalBilinear s t f g X‖ ≤
      (X/(a*b))*M*(∫ x : ℝ, ‖g x‖ ∂spectralKLPhysicalMeasure) := by
  let D := (X/(a*b))*M
  have hI := spectralWeylFoldDensity_compact_integrable hX s t f g hf hfc hfp hg hgc hgp
  have hU : ∀ᵐ q ∂spectralWeylFoldMeasure, q.2 ∈ Ioo (0 : ℝ) 1 := by
    unfold spectralWeylFoldMeasure
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioo)
  have hbnd : ∀ᵐ q ∂spectralWeylFoldMeasure, ‖spectralWeylFoldDensity s t f g X q‖ ≤ D*‖g q.1‖ := by
    filter_upwards [hU] with q hq
    have h := spectralWeylFoldDensity_compact_bound (x := q.1) ha hb hX le_rfl le_rfl hq s t f g hflo hglo hM
    have he : X^2/(X*a*b) = X/(a*b) := by field_simp [hX.ne',ha.ne',hb.ne']
    rwa [he] at h
  have huI : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hD : Integrable (fun q : ℝ × ℝ => D*‖g q.1‖) spectralWeylFoldMeasure := by
    simpa only [spectralWeylFoldMeasure,mul_one] using
      (((spectralKLPhysical_compact_integrable g hg hgc hgp).norm.const_mul D).mul_prod huI)
  rw [spectralWeylPhysicalBilinear_fold hX s t f g hf.measurable hg.measurable hI]
  unfold spectralWeylFoldBilinear
  calc
    _ ≤ ∫ q : ℝ × ℝ, ‖spectralWeylFoldDensity s t f g X q‖ ∂spectralWeylFoldMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ q : ℝ × ℝ, D*‖g q.1‖ ∂spectralWeylFoldMeasure := integral_mono_ae hI.norm hD hbnd
    _ = _ := by
      change (∫ q : ℝ × ℝ, D*‖g q.1‖ ∂spectralWeylFoldMeasure) =
        D*(∫ x : ℝ, ‖g x‖ ∂spectralKLPhysicalMeasure)
      unfold spectralWeylFoldMeasure at hD ⊢
      rw [integral_prod _ hD,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [setIntegral_const,measureReal_def,Real.volume_Ioo]
      norm_num

theorem spectralKLHeightPhysicalTest_one (ρ : ℝ → ℝ) :
    spectralKLHeightPhysicalTest 1 ρ = spectralKLHeightBaseTest ρ := by
  funext x
  simp only [spectralKLHeightPhysicalTest,div_one]

theorem cuspWeylOrbitalKernel_compact_norm_bound (N : ℕ) [NeZero N] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hη : Continuous η) (hcη : HasCompactSupport η) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B C M : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hM : ∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η C) {p : ℝ × ℝ | 0 < p.2}) :
    ‖cuspWeylOrbitalKernel N m n ρ η C hC.ne'‖ ≤
      (2/(C^3*(A*B)))*M*(∫ y : ℝ, ‖spectralKLHeightBaseTest ρ y‖ ∂spectralKLPhysicalMeasure) := by
  rw [cuspWeylOrbitalKernel_frequency_physical N m n ρ η hρ hcρ hpρ hη hcη hpη zero_lt_one zero_lt_one hC hI]
  simp only [one_mul,Real.sqrt_one,div_one,spectralKLHeightPhysicalTest_one]
  obtain ⟨hf,hfc,hfp⟩ := spectralKLHeightBaseTest_properties η hη hcη hpη
  obtain ⟨hg,hgc,hgp⟩ := spectralKLHeightBaseTest_properties ρ hρ hcρ hpρ
  have hflo (z : ℝ) (hz : z ∈ tsupport (spectralKLHeightBaseTest η)) : B ≤ z :=
    hηlo z (spectralKLHeightBaseTest_tsupport η hz)
  have hglo (y : ℝ) (hy : y ∈ tsupport (spectralKLHeightBaseTest ρ)) : A ≤ y :=
    hρlo y (spectralKLHeightBaseTest_tsupport ρ hy)
  have hbnd := spectralWeylPhysicalBilinear_compact_norm_bound (div_pos two_pos hC) hB hA
    (cuspFourierFrequency (N : ℝ) m) (cuspFourierFrequency (N : ℝ) n)
    (spectralKLHeightBaseTest η) (spectralKLHeightBaseTest ρ) hf hfc hfp hg hgc hgp hflo hglo hM
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 1/C^2)]
  refine (mul_le_mul_of_nonneg_left hbnd (by positivity : 0 ≤ 1/C^2)).trans_eq ?_
  field_simp [hC.ne',hA.ne',hB.ne']

end ArtinMatthews
