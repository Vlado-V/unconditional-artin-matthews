module

public import ArtinMatthews.SpectralStoneContinuousMeasure
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

/-! The true critical parameter gives the exact positive-frequency density
of the genuine regular ambient spectral measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal MatrixGroups
namespace ArtinMatthews

def spectralStoneEnergyFromFrequency (t : ℝ) : ℝ := 1/4+t^2

theorem spectralStoneEnergyFromFrequency_deriv (t : ℝ) :
    HasDerivAt spectralStoneEnergyFromFrequency (2*t) t := by
  change HasDerivAt (fun x : ℝ => 1/4+x^2) (2*t) t
  simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using
    (hasDerivAt_pow 2 t).const_add (1/4)

theorem spectralStoneEnergyFromFrequency_injOn : InjOn spectralStoneEnergyFromFrequency (Ioi 0) := by
  intro a ha b hb he
  change 0<a at ha
  change 0<b at hb
  have hs : a^2=b^2 := add_left_cancel he
  rcases lt_trichotomy a b with h | h | h
  · nlinarith [mul_pos (sub_pos.mpr h) (add_pos ha hb)]
  · exact h
  · nlinarith [mul_pos (sub_pos.mpr h) (add_pos ha hb)]

theorem spectralStoneEnergyFromFrequency_image :
    spectralStoneEnergyFromFrequency '' Ioi 0=Ioi (1/4 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    change 0<t at ht
    change (1/4:ℝ)<1/4+t^2
    nlinarith [sq_pos_of_pos ht]
  · intro hx
    have hp : 0<x-1/4 := sub_pos.mpr hx
    refine ⟨Real.sqrt (x-1/4),Real.sqrt_pos.mpr hp,?_⟩
    rw [spectralStoneEnergyFromFrequency,Real.sq_sqrt hp.le]
    ring

theorem gamma0StoneEnergyFromFrequency_ae_good (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    ∀ᵐ t ∂(volume.restrict (Ioi 0)),spectralStoneEnergyFromFrequency t∈gamma0StoneGoodEnergy N ψ Y := by
  let U := gamma0StoneGoodEnergy N ψ Y
  let A := Ioi 0 ∩ spectralStoneEnergyFromFrequency ⁻¹' Uᶜ
  have hmaps : MapsTo spectralStoneEnergyFromFrequency A Uᶜ := fun _ ht => ht.2
  have hcount : A.Countable := hmaps.countable_of_injOn
    (spectralStoneEnergyFromFrequency_injOn.mono inter_subset_left)
    (gamma0StoneGoodEnergy_compl_countable N ψ Y)
  have hz : volume A=0 := hcount.measure_zero volume
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t∉A :=
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hz)
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi,ae_restrict_of_ae hae] with t ht hA
  by_contra h
  exact hA ⟨ht,h⟩

def gamma0StoneFrequencyDensity (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (t : ℝ) : ℝ :=
  (∑ i,‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i)
    ψ (eisensteinCriticalPoint t)‖^2)/(2*Real.pi)

theorem gamma0StoneFrequencyDensity_nonneg (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (t : ℝ) :
    0≤gamma0StoneFrequencyDensity N ψ t := by
  unfold gamma0StoneFrequencyDensity
  positivity

theorem gamma0StoneFrequencyDensity_ae_change (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0StoneFrequencyDensity N ψ =ᵐ[volume.restrict (Ioi 0)]
      (fun t => |2*t| * gamma0StoneDensityExtension N ψ Y (spectralStoneEnergyFromFrequency t)) := by
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi,
    gamma0StoneEnergyFromFrequency_ae_good N ψ Y] with t ht hg
  change 0<t at ht
  have hx : (1/4:ℝ)<spectralStoneEnergyFromFrequency t := by
    unfold spectralStoneEnergyFromFrequency
    linarith [sq_pos_of_pos ht]
  rw [gamma0StoneDensityExtension,indicator_of_mem hg,gamma0StoneBoundaryDensity_supercritical N ψ Y _ hg hx]
  have hsq : spectralStoneEnergyFromFrequency t-1/4=t^2 := by
    unfold spectralStoneEnergyFromFrequency
    ring
  rw [hsq,Real.sqrt_sq ht.le,abs_of_pos (mul_pos (by norm_num) ht),gamma0StoneFrequencyDensity]
  field_simp [ht.ne',Real.pi_ne_zero]
  ring

theorem gamma0StoneFrequencyDensity_aemeasurable (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    AEMeasurable (gamma0StoneFrequencyDensity N ψ) (volume.restrict (Ioi 0)) := by
  have henergy : Continuous spectralStoneEnergyFromFrequency :=
    continuous_const.add (continuous_id.pow 2)
  have hw : Measurable (fun t : ℝ => |2*t|) :=
    (continuous_const.mul continuous_id).abs.measurable
  exact (hw.mul ((gamma0StoneDensityExtension_measurable N ψ Y).comp henergy.measurable)).aemeasurable.congr
    (gamma0StoneFrequencyDensity_ae_change N ψ Y).symm

theorem gamma0StoneContinuousMeasure_univ_frequency (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    gamma0StoneContinuousMeasure N ψ Y univ=
      ∫⁻ t in Ioi 0,ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t) := by
  let g := gamma0StoneDensityExtension N ψ Y
  have hsupport : (Ioi (1/4:ℝ)).indicator (fun x => ENNReal.ofReal (g x))=
      (fun x => ENNReal.ofReal (g x)) := by
    funext x
    by_cases hx : x∈Ioi (1/4:ℝ)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      change 0=ENNReal.ofReal (gamma0StoneDensityExtension N ψ Y x)
      rw [gamma0StoneDensityExtension_zero_below N ψ Y x (le_of_not_gt hx),ENNReal.ofReal_zero]
  rw [gamma0StoneContinuousMeasure_eq_withDensity N ψ Y,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (∫⁻ x,ENNReal.ofReal (g x))=_
  rw [← hsupport,lintegral_indicator measurableSet_Ioi,← spectralStoneEnergyFromFrequency_image,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun t _ => (spectralStoneEnergyFromFrequency_deriv t).hasDerivWithinAt)
      spectralStoneEnergyFromFrequency_injOn]
  apply lintegral_congr_ae
  filter_upwards [gamma0StoneFrequencyDensity_ae_change N ψ Y] with t ht
  rw [ht,ENNReal.ofReal_mul (abs_nonneg (2*t))]

end ArtinMatthews
