module

public import ArtinMatthews.SpectralWeylFoldDomination
public import ArtinMatthews.SpectralWeylPhysicalContinuity
public import ArtinMatthews.SpectralWeylPowerFold
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Absolute integrability of the actual two-height orbital kernel with
one noncompact power-decaying input and one compact positive-height test. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem spectralFoldEndpointPower_integrable {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun u : ℝ => (1-u)^(B-1)) (Ioo (0 : ℝ) 1) := by
  have h : IntervalIntegrable (fun u : ℝ => u^(B-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have ht := h.comp_sub_left 1
  simpa only [sub_zero,sub_self] using ht.2.mono_set Ioo_subset_Ioc_self

theorem spectralWeylFoldDensity_power_integrable {X B M : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure := by
  obtain ⟨b,hb,hglo⟩ := spectral_compact_positive_lower_bound g hgc hgp
  let C := (4/X)*M*(X^2/(4*b))^B
  have hi := ((spectralKLPhysical_compact_integrable g hg hgc hgp).norm.const_mul C).mul_prod
    (spectralFoldEndpointPower_integrable hB)
  have hpos : ∀ᵐ q ∂spectralWeylFoldMeasure,
      0 < q.1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
    unfold spectralWeylFoldMeasure
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact ⟨hx,hu⟩
  apply hi.mono' (spectralWeylFoldDensity_measurable s t X f g hfm hg.measurable).aestronglyMeasurable
  filter_upwards [hpos] with q hq
  refine (spectralWeylFoldDensity_compact_power_bound hX hb hq.2 hB hB₁ hM s t q.1 hq.1
    f g hf hglo).trans_eq ?_
  dsimp only [C]
  ring

theorem spectralWeylPhysicalIntegrand_power_integrable {X B M : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Integrable (fun q : ℝ × ℝ => spectralWeylPhysicalIntegrand s t f g (q,X))
      (spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure) :=
  spectralWeylPhysicalIntegrand_integrable_of_fold hX s t f g hfm hg.measurable
    (spectralWeylFoldDensity_power_integrable hX hB hB₁ hM s t f g hfm hg hgc hgp hf)

end ArtinMatthews
