module

public import ArtinMatthews.SpectralKLRealKernel
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact spectral synthesis and its absolutely integrable
regularized products. The real kernel is identified with Schlafli K_it. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralKLSynthesis (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, (spectralKLRealKernel t x : ℂ)*f t

theorem spectralKLSynthesis_stronglyMeasurable (f : ℝ → ℂ) (hf : Continuous f) :
    StronglyMeasurable (spectralKLSynthesis f) := by
  have hK := spectralKLRealKernel_stronglyMeasurable.measurable.comp
    (measurable_swap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ))
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => (spectralKLRealKernel p.2 p.1 : ℂ)*f p.2) :=
    ((Complex.continuous_ofReal.measurable.comp hK).mul (hf.measurable.comp measurable_snd)).stronglyMeasurable
  exact hm.integral_prod_right'

theorem spectralKLSynthesis_integrand_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (spectralKLRealKernel t x : ℂ)*f t) := by
  have hK := spectralKLRealKernel_stronglyMeasurable.measurable.comp
    (show Measurable (fun t : ℝ => (t,x)) by fun_prop)
  have hm := (Complex.continuous_ofReal.measurable.comp hK).mul hf.measurable
  apply ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul (spectralKLRealKernel 0 x)).mono'
    hm.aestronglyMeasurable
  filter_upwards with t
  dsimp only [Function.comp_apply,Pi.mul_apply]
  rw [norm_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (spectralKLRealKernel_norm_le_zero t hx) (norm_nonneg _)

theorem spectralKLSynthesis_norm_bound (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) {x : ℝ} (hx : 0 < x) :
    ‖spectralKLSynthesis f x‖ ≤ spectralKLRealKernel 0 x*(∫ t : ℝ, ‖f t‖) := by
  calc
    _ ≤ ∫ t : ℝ, spectralKLRealKernel 0 x*‖f t‖ := by
      apply norm_integral_le_of_norm_le
        ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul (spectralKLRealKernel 0 x))
      filter_upwards with t
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (spectralKLRealKernel_norm_le_zero t hx) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem spectralKLSynthesis_actual (f : ℝ → ℂ) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) :
    spectralKLSynthesis f x = ∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*f t := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
    have hn : t ∉ tsupport f := fun h => ht (hfp h)
    simp [image_eq_zero_of_notMem_tsupport hn])]
  unfold spectralKLSynthesis
  apply integral_congr_ae
  filter_upwards with t
  rw [schlafliBesselK_imaginary_eq_realKernel t hx]

theorem spectralKLSynthesis_conj (f : ℝ → ℂ) (x : ℝ) :
    spectralKLSynthesis (fun t => star (f t)) x = star (spectralKLSynthesis f x) := by
  unfold spectralKLSynthesis
  have hc := integral_conj (μ := volume) (f := fun t : ℝ => (spectralKLRealKernel t x : ℂ)*f t)
  simp only [starRingEnd_apply] at hc
  rw [← hc]
  apply integral_congr_ae
  filter_upwards with t
  simp

theorem spectralKLSynthesis_regularized_energy_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => x^(ε-1)*‖spectralKLSynthesis f x‖^2) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x^(ε-1)*‖spectralKLSynthesis f x‖^2)
      (volume.restrict (Ioi 0)) :=
    (show Measurable (fun x : ℝ => x^(ε-1)) by fun_prop).aestronglyMeasurable.mul
      ((spectralKLSynthesis_stronglyMeasurable f hf).norm.pow 2).aestronglyMeasurable
  apply ((spectralKLRealKernel_zero_energy_integrable ε hε).mul_const
    ((∫ t : ℝ, ‖f t‖)^2)).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _))]
  have hb := spectralKLSynthesis_norm_bound f hf hfc hx
  calc
    _ ≤ x^(ε-1)*(spectralKLRealKernel 0 x*(∫ t : ℝ, ‖f t‖))^2 := by
      gcongr
      exact Real.rpow_nonneg hx.le _
    _ = _ := by ring

def spectralKLSynthesisProductKernel (f g : ℝ → ℂ) (ε : ℝ) (x : ℝ) (p : ℝ × ℝ) : ℂ :=
  (x^(ε-1) : ℝ) * ((spectralKLRealKernel p.1 x : ℂ)*f p.1)*
    ((spectralKLRealKernel p.2 x : ℂ)*g p.2)

theorem spectralKLSynthesisProductKernel_integrable (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => spectralKLSynthesisProductKernel f g ε q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (volume.prod volume)) := by
  have hK1 := spectralKLRealKernel_stronglyMeasurable.measurable.comp
    (show Measurable (fun q : ℝ × (ℝ × ℝ) => (q.2.1,q.1)) by fun_prop)
  have hK2 := spectralKLRealKernel_stronglyMeasurable.measurable.comp
    (show Measurable (fun q : ℝ × (ℝ × ℝ) => (q.2.2,q.1)) by fun_prop)
  have hm : AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => spectralKLSynthesisProductKernel f g ε q.1 q.2)
      ((volume.restrict (Ioi 0)).prod (volume.prod volume)) := by
    apply Measurable.aestronglyMeasurable
    unfold spectralKLSynthesisProductKernel
    exact ((Complex.continuous_ofReal.measurable.comp (by fun_prop)).mul
      ((Complex.continuous_ofReal.measurable.comp hK1).mul (hf.measurable.comp (by fun_prop)))).mul
      ((Complex.continuous_ofReal.measurable.comp hK2).mul (hg.measurable.comp (by fun_prop)))
  have hfi : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
  have hgi : Integrable g volume := hg.integrable_of_hasCompactSupport hgc
  have hi := (spectralKLRealKernel_zero_energy_integrable ε hε).mul_prod (hfi.norm.mul_prod hgi.norm)
  apply hi.mono' hm
  have hxp : ∀ᵐ q : ℝ × (ℝ × ℝ) ∂((volume.restrict (Ioi 0)).prod (volume.prod volume)), 0 < q.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  filter_upwards [hxp] with q hx
  unfold spectralKLSynthesisProductKernel
  simp only [norm_mul,Complex.norm_real]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  have hz : 0 ≤ spectralKLRealKernel 0 q.1 := spectralKLRealKernel_zero_nonneg
  calc
    _ = q.1^(ε-1)*(‖spectralKLRealKernel q.2.1 q.1‖*‖spectralKLRealKernel q.2.2 q.1‖)*
        (‖f q.2.1‖*‖g q.2.2‖) := by ring
    _ ≤ q.1^(ε-1)*(spectralKLRealKernel 0 q.1*spectralKLRealKernel 0 q.1)*
        (‖f q.2.1‖*‖g q.2.2‖) := by
      gcongr
      · exact spectralKLRealKernel_norm_le_zero q.2.1 hx
      · exact spectralKLRealKernel_norm_le_zero q.2.2 hx
    _ = _ := by ring

end ArtinMatthews
