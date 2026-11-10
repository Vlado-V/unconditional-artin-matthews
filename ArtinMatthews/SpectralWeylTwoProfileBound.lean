module

public import ArtinMatthews.SpectralWeylWeightedMoment
public import ArtinMatthews.SpectralWeylFoldDomination
public import ArtinMatthews.SpectralKLMacdonaldSpectralFubini
public import ArtinMatthews.SpectralWeylPhysicalContinuity
public import ArtinMatthews.SpectralWeylPowerFold
public import ArtinMatthews.SpectralWeylPowerIntegrable
public import ArtinMatthews.SpectralWeylPowerNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The weighted second-profile moment controls the full folded kernel
without a compact-support condition on either profile. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem spectralWeylFoldDensity_weighted_power_bound {X x u B M : ℝ}
    (hX : 0 < X) (hx : 0 < x) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hB₁ : B ≤ 1) (hM : 0 ≤ M) (s t : ℝ) (f g : ℝ → ℂ)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    ‖spectralWeylFoldDensity s t f g X (x,u)‖ ≤
      ((4/X)*M*(X^2/4)^B)*(x^(-B)*‖g x‖)*(1-u)^(B-1) := by
  have hv : 0 < 1-u := sub_pos.mpr hu.2
  have hp : (1-u^2)^(B-1) ≤ (1-u)^(B-1) :=
    Real.rpow_le_rpow_of_nonpos hv (by nlinarith [hu.1,hu.2]) (sub_nonpos.mpr hB₁)
  have hfactor : (X^2/(4*x))^B = (X^2/4)^B*x^(-B) := by
    rw [show X^2/(4*x) = (X^2/4)/x by rw [div_div]]
    rw [Real.div_rpow (by positivity) hx.le,Real.rpow_neg hx.le]
    ring
  calc
    _ ≤ (4/X)*M*(X^2/(4*x))^B*(1-u^2)^(B-1)*‖g x‖ :=
      spectralWeylFoldDensity_power_bound hX hx hu hM s t f g hf
    _ = ((4/X)*M*(X^2/4)^B)*(x^(-B)*‖g x‖)*(1-u^2)^(B-1) := by
      rw [hfactor]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem spectralWeylPhysicalBilinear_moment_bound {X B M : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure ∧
    Integrable (fun q : ℝ × ℝ => spectralWeylPhysicalIntegrand s t f g (q,X))
      (spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure) ∧
    ‖spectralWeylPhysicalBilinear s t f g X‖ ≤
      ((4/X)*M*(X^2/4)^B)*
        (spectralWeylPhysicalMoment B g*∫ u in Ioo (0 : ℝ) 1, (1-u)^(B-1)) := by
  let C := (4/X)*M*(X^2/4)^B
  have hi := (hMoment.const_mul C).mul_prod (spectralFoldEndpointPower_integrable hB)
  have hpos : ∀ᵐ q ∂spectralWeylFoldMeasure, 0 < q.1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
    unfold spectralWeylFoldMeasure
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact ⟨hx,hu⟩
  have hbnd : ∀ᵐ q ∂spectralWeylFoldMeasure,
      ‖spectralWeylFoldDensity s t f g X q‖ ≤
        (C*(q.1^(-B)*‖g q.1‖))*(1-q.2)^(B-1) := by
    filter_upwards [hpos] with q hq
    exact spectralWeylFoldDensity_weighted_power_bound hX hq.1 hq.2 hB₁ hM s t f g hf
  have hI : Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure :=
    hi.mono' (spectralWeylFoldDensity_measurable s t X f g hfm hgm).aestronglyMeasurable hbnd
  refine ⟨hI,spectralWeylPhysicalIntegrand_integrable_of_fold hX s t f g hfm hgm hI,?_⟩
  rw [spectralWeylPhysicalBilinear_fold hX s t f g hfm hgm hI]
  refine (norm_integral_le_of_norm_le hi hbnd).trans_eq ?_
  rw [integral_prod_mul (fun x : ℝ => C*(x^(-B)*‖g x‖))
    (fun u : ℝ => (1-u)^(B-1)),integral_const_mul]
  dsimp only [C,spectralWeylPhysicalMoment]
  ring

theorem spectralWeylPhysicalBilinear_uniform_moment_bound {B M : ℝ}
    (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M) (g : ℝ → ℂ) (hgm : Measurable g)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖g x‖) spectralKLPhysicalMeasure) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X, 0 < X → ∀ s t : ℝ, ∀ f : ℝ → ℂ,
      Measurable f → (∀ z, 0 < z → ‖f z‖ ≤ M*z^B) →
      ‖spectralWeylPhysicalBilinear s t f g X‖ ≤ D*X^(2*B-1) := by
  let J := spectralWeylPhysicalMoment B g*∫ u in Ioo (0 : ℝ) 1, (1-u)^(B-1)
  have hJ : 0 ≤ J := mul_nonneg (spectralWeylPhysicalMoment_nonneg B g)
    (setIntegral_nonneg measurableSet_Ioo (fun u hu => Real.rpow_nonneg (by linarith [hu.2]) _))
  refine ⟨4*M/4^B*J,by positivity,?_⟩
  intro X hX s t f hfm hf
  refine (spectralWeylPhysicalBilinear_moment_bound hX hB hB₁ hM s t f g hfm hgm hMoment hf).2.2.trans_eq ?_
  simpa only [mul_one] using spectralWeyl_power_prefactor hX zero_lt_one B M J

end ArtinMatthews
