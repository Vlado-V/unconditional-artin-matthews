module

public import ArtinMatthews.SpectralStoneFrequency
public import ArtinMatthews.SpectralStoneEisensteinPair
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

/-! The genuine scalar continuous spectral measure is the pushforward
of the normalized positive-frequency Eisenstein density. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace ArtinMatthews

theorem gamma0StoneFrequencyDensity_measurable (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    Measurable (gamma0StoneFrequencyDensity N ψ) := by
  change Measurable (fun t => (∑ i,‖gamma0StoneEisensteinAmplitude N ψ i t‖^2)/(2*Real.pi))
  exact (Finset.measurable_sum _ (fun i _ => (gamma0StoneEisensteinAmplitude_measurable N ψ i).norm.pow_const 2)).div_const _

def gamma0StoneFrequencyMeasure (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t))

theorem gamma0StoneDensity_weighted_change (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (a : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi (1/4:ℝ),a x*ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x))=
      ∫⁻ t in Ioi 0,a (spectralStoneEnergyFromFrequency t)*ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t) := by
  rw [← spectralStoneEnergyFromFrequency_image,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun t _ => (spectralStoneEnergyFromFrequency_deriv t).hasDerivWithinAt)
      spectralStoneEnergyFromFrequency_injOn]
  apply lintegral_congr_ae
  filter_upwards [gamma0StoneFrequencyDensity_ae_change N ψ Y] with t ht
  rw [ht,ENNReal.ofReal_mul (abs_nonneg (2*t))]
  ac_rfl

theorem gamma0StoneContinuousMeasure_lintegral_frequency (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (a : ℝ → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ x,a x ∂gamma0StoneContinuousMeasure N ψ Y)=
      ∫⁻ t in Ioi 0,a (spectralStoneEnergyFromFrequency t)*ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t) := by
  rw [gamma0StoneContinuousMeasure_eq_withDensity N ψ Y,
    lintegral_withDensity_eq_lintegral_mul _ (gamma0StoneDensityExtension_measurable N ψ Y).ennreal_ofReal ha]
  simp only [Pi.mul_apply]
  have he : (Ioi (1/4:ℝ)).indicator
      (fun x => a x*ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x))=
        (fun x => a x*ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x)) := by
    funext x
    by_cases hx : x∈Ioi (1/4:ℝ)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,gamma0StoneDensityExtension_zero_below N ψ Y x (le_of_not_gt hx),
        ENNReal.ofReal_zero,mul_zero]
  calc
    _ = ∫⁻ x,a x*ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x) := by
      apply lintegral_congr
      intro x
      exact mul_comm _ _
    _ = ∫⁻ x in Ioi (1/4:ℝ),a x*ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x) := by
      have hi := lintegral_indicator (μ:=volume) (s:=Ioi (1/4:ℝ)) measurableSet_Ioi
        (fun x => a x*ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x))
      rw [he] at hi
      exact hi
    _ = _ := gamma0StoneDensity_weighted_change N ψ Y a

theorem gamma0StoneContinuousMeasure_eq_frequency_map (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0StoneContinuousMeasure N ψ Y=
      Measure.map spectralStoneEnergyFromFrequency (gamma0StoneFrequencyMeasure N ψ) := by
  apply Measure.ext_of_lintegral
  intro a ha
  have he : Measurable spectralStoneEnergyFromFrequency :=
    (continuous_const.add (continuous_id.pow 2)).measurable
  rw [lintegral_map ha he,gamma0StoneFrequencyMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (gamma0StoneFrequencyDensity_measurable N ψ).ennreal_ofReal
    (show Measurable (fun t => a (spectralStoneEnergyFromFrequency t)) from ha.comp he),
    gamma0StoneContinuousMeasure_lintegral_frequency N ψ Y a ha]
  apply lintegral_congr
  intro t
  exact mul_comm _ _

theorem gamma0StoneContinuousMeasure_integral_frequency (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (a : ℝ → ℂ)
    (ha : Integrable a (gamma0StoneContinuousMeasure N ψ Y)) :
    (∫ x,a x ∂gamma0StoneContinuousMeasure N ψ Y)=
      ∫ t in Ioi 0,(gamma0StoneFrequencyDensity N ψ t:ℂ)*a (spectralStoneEnergyFromFrequency t) := by
  have he : Measurable spectralStoneEnergyFromFrequency :=
    (continuous_const.add (continuous_id.pow 2)).measurable
  have hmeas : AEStronglyMeasurable a
      (Measure.map spectralStoneEnergyFromFrequency (gamma0StoneFrequencyMeasure N ψ)) := by
    rw [← gamma0StoneContinuousMeasure_eq_frequency_map N ψ Y]
    exact ha.aestronglyMeasurable
  rw [gamma0StoneContinuousMeasure_eq_frequency_map N ψ Y,
    integral_map he.aemeasurable hmeas,gamma0StoneFrequencyMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (gamma0StoneFrequencyDensity_measurable N ψ).ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change (ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t)).toReal •
      a (spectralStoneEnergyFromFrequency t)=_
    rw [ENNReal.toReal_ofReal (gamma0StoneFrequencyDensity_nonneg N ψ t),Complex.real_smul])

end ArtinMatthews
