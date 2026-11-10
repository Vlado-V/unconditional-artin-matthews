module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedRootBoxLipschitz
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ArtinMatthews.MarkedMemoryPathCapacityGeometry
public import ArtinMatthews.MarkedPhysicalCoordinateGoodVolume
public import ArtinMatthews.MarkedTypeIICollisionDecay
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The exact full-band baseline product and normalized root measure
cost in the quantitative capped boundary estimate. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators

theorem markedMemoryActualBaselineProduct_bounds
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ q : ℝ,0≤q → q≤1 →
      0≤(∏ j,∏ p : markedRawActualPrimeBand e x j,
        markedMemoryBaseline q (markedMemoryMomentLength x) p.1) ∧
      (∏ j,∏ p : markedRawActualPrimeBand e x j,
        markedMemoryBaseline q (markedMemoryMomentLength x) p.1)≤1 := by
  filter_upwards [markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hn hlog
  intro q hq₀ hq₁
  apply markedMemoryPathBaselineProduct_bounds q hq₀ hq₁
  intro j p
  have hm : (p.1:ℕ)∈markedLogPowerBand (e j) x := (mem_markedRawPrimeBand _ p.1).mp p.2
  exact hn _ (marked_band_common_lower (he j) hlog hm)

theorem markedNormalizedRoot_integral_norm_le
    (f : (ℝ × (ℝ × ℝ)) → ℂ) (C : ℝ)
    (hf : ∀ p∈markedRootBoxDomain,‖f p‖≤C) :
    ‖∫ p,f p ∂markedNormalizedRootMeasure‖≤15*C := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  have hae : ∀ᵐ p ∂markedNormalizedRootMeasure,p∈markedRootBoxDomain := by
    unfold markedNormalizedRootMeasure markedRootBoxDomain
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun p : ℝ × (ℝ × ℝ) => p.1∈Set.Icc (0:ℝ) 1 ∧
        p.2.1∈Set.Icc (1:ℝ) 16 ∧ p.2.2∈Set.Icc (1:ℝ) 2) (by measurability)).2
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with r hr
    simp only [hr,true_and]
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun p : ℝ × ℝ => p.1∈Set.Icc (1:ℝ) 16 ∧ p.2∈Set.Icc (1:ℝ) 2)
      (by measurability)).2
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with a ha
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with b hb
    exact ⟨ha,hb⟩
  have h := norm_integral_le_of_norm_le_const (hae.mono (fun p hp => hf p hp))
  simpa only [Measure.real,markedNormalizedRootMeasure_univ,ENNReal.toReal_ofNat,mul_comm] using h

end ArtinMatthews
