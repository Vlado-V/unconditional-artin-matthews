module

public import ArtinMatthews.CuspAverageProjectionOperator
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.CuspAverageHyperbolicTransport
public import ArtinMatthews.SpectralCuspVerticalTesting
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Exact cancellation of the hyperbolic density in compact plane-test
pairings.  The identities retain the actual unnormalized strip measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace ArtinMatthews

theorem cuspStripMeasure_le_smul_volume (w : ℝ) {Y : ℝ} (hY : 0 < Y) :
    cuspStripMeasure w Y ≤ ENNReal.ofReal (Y^(-2:ℤ)) • volume := by
  calc
    _ ≤ volume.prod (ENNReal.ofReal (Y^(-2:ℤ)) • volume) :=
      Measure.prod_mono Measure.restrict_le_self (cuspVerticalMeasure_le_smul_volume hY)
    _ = _ := by rw [Measure.prod_smul_right]; rfl

theorem cuspStrip_memLp_compact (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    {t : ℝ × ℝ → ℂ} (ht : Continuous t) (hc : HasCompactSupport t) :
    MemLp t 2 (cuspStripMeasure w Y) :=
  (ht.memLp_of_hasCompactSupport hc (μ := volume)).of_measure_le_smul
    ENNReal.ofReal_ne_top (cuspStripMeasure_le_smul_volume w hY)

theorem cuspStrip_integral_density (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × ℝ → E) :
    (∫ p, F p ∂cuspStripMeasure w Y) =
      ∫ p in Ioc 0 w ×ˢ Ioi Y, (p.2^(-2:ℤ)) • F p := by
  rw [cuspStripMeasure_eq_density, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
  rw [ENNReal.toReal_ofReal (zpow_nonneg (hY.trans hp.2).le (-2:ℤ))]

theorem cuspStrip_integral_height_cancel (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ × ℝ → ℝ) (f : ℝ × ℝ → E)
    (hs : Function.support t ⊆ Ioc 0 w ×ˢ Ioi Y) :
    (∫ p, (p.2^2*t p) • f p ∂cuspStripMeasure w Y) = ∫ p, t p • f p := by
  rw [cuspStrip_integral_density w hY]
  calc
    _ = ∫ p in Ioc 0 w ×ˢ Ioi Y, t p • f p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
      have hp0 : p.2 ≠ 0 := (hY.trans hp.2).ne'
      rw [smul_smul]
      congr 1
      rw [zpow_neg, zpow_ofNat]
      field_simp
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
      have ht : t p = 0 := by
        by_contra hn
        exact hp (hs hn)
      rw [ht,zero_smul]

theorem cuspStrip_integral_compact_density (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ × ℝ → ℝ) (f : ℝ × ℝ → E)
    (hs : Function.support t ⊆ Ioc 0 w ×ˢ Ioi Y) :
    (∫ p, t p • f p ∂cuspStripMeasure w Y) =
      ∫ p, (p.2^(-2:ℤ)*t p) • f p := by
  rw [cuspStrip_integral_density w hY]
  simp_rw [smul_smul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have ht : t p = 0 := by
    by_contra hn
    exact hp (hs hn)
  rw [ht,mul_zero,zero_smul]

theorem cuspStrip_compact_pairing_integrable (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    {t : ℝ × ℝ → ℝ} (ht : Continuous t) (hc : HasCompactSupport t)
    (f : CuspStripL2 w Y) :
    Integrable (fun p => t p • f p) (cuspStripMeasure w Y) := by
  have hm : MemLp (fun p => (t p : ℂ)) 2 (cuspStripMeasure w Y) :=
    cuspStrip_memLp_compact w hY (Complex.continuous_ofReal.comp ht)
      (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
  have hi := L2.integrable_inner (𝕜 := ℂ) (hm.toLp (fun p => (t p : ℂ))) f
  apply hi.congr
  filter_upwards [hm.coeFn_toLp] with p hp
  rw [hp]
  simp only [RCLike.inner_apply,Complex.conj_ofReal,Complex.real_smul,mul_comm]

theorem cuspStrip_real_projection_pairing (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    {t : ℝ × ℝ → ℝ} (ht : Continuous t) (hc : HasCompactSupport t)
    (L : ℂ →L[ℝ] ℝ) (f : CuspStripL2 w Y) :
    L (∫ p, t p • f p ∂cuspStripMeasure w Y) =
      ∫ p, t p * L (f p) ∂cuspStripMeasure w Y := by
  rw [← L.integral_comp_comm (cuspStrip_compact_pairing_integrable w hY ht hc f)]
  congr 1
  funext p
  exact L.map_smul (t p) (f p)

end ArtinMatthews
