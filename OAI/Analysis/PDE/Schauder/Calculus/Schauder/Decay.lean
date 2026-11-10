module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonInverse
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Decay at infinity of the actual Newtonian and Poisson solutions. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem compactSupport_tendsto_zero {E : Type*} [TopologicalSpace E]
    (f : E → ℝ) (hfc : HasCompactSupport f) : Tendsto f (cocompact E) (𝓝 0) := by
  have he : f =ᶠ[cocompact E] (fun _ => 0) := by
    filter_upwards [hfc.isCompact.compl_mem_cocompact] with x hx
    by_contra h
    exact hx (subset_closure h)
  exact tendsto_const_nhds.congr' he.symm

theorem newtonianPotential_far_bound {m : ℕ} (hm : 3 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Integrable f)
    {R : ℝ} (hR : 0 < R) (hs : Function.support f ⊆ ball 0 R)
    (x : EuclideanSpace ℝ (Fin m)) (hx : 2 * R ≤ ‖x‖) :
    |newtonianPotential f x| ≤ (‖x‖ / 2) ^ (2 - (m : ℝ)) * ∫ y, |f y| := by
  have he : newtonianPotential f x = ∫ y, newtonianKernel m (x - y) * f y := by
    have h := integral_sub_left_eq_self (fun y => newtonianKernel m y * f (x - y)) volume x
    simpa only [sub_sub_cancel, newtonianPotential] using h.symm
  rw [he]
  have hi : Integrable (fun y => (‖x‖ / 2) ^ (2 - (m : ℝ)) * |f y|) := hf.norm.const_mul _
  have hb : ∀ᵐ y, ‖newtonianKernel m (x - y) * f y‖ ≤
      (‖x‖ / 2) ^ (2 - (m : ℝ)) * |f y| := by
    filter_upwards with y
    by_cases hy : f y = 0
    · simp [hy]
    have hyn : ‖y‖ < R := by simpa using hs hy
    have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
      have ht := norm_sub_norm_le x y
      linarith
    have hxpos : 0 < ‖x‖ / 2 := by linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, newtonianKernel_eq_norm_rpow,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hxpos hxy (by
        have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
        linarith))
      (abs_nonneg _)
  simpa only [integral_const_mul, Real.norm_eq_abs] using norm_integral_le_of_norm_le hi hb

theorem newtonianPotential_tendsto_zero {m : ℕ} (hm : 3 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (newtonianPotential f) (cocompact (EuclideanSpace ℝ (Fin m))) (𝓝 0) := by
  obtain ⟨R, hR, hs⟩ := hfc.isCompact.isBounded.subset_ball_lt 0 0
  have hsupport : Function.support f ⊆ ball 0 R := subset_closure.trans hs
  have hp : 0 < (m : ℝ) - 2 := by
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have ht : Tendsto (fun x : EuclideanSpace ℝ (Fin m) => (‖x‖ / 2) ^ (2 - (m : ℝ)))
      (cocompact _) (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hp).comp
      (Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
        (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin m))))
    change Tendsto (fun x : EuclideanSpace ℝ (Fin m) => (‖x‖ / 2) ^ (-((m : ℝ) - 2)))
      (cocompact _) (𝓝 0) at h
    simpa only [neg_sub] using h
  have hev : ∀ᶠ x : EuclideanSpace ℝ (Fin m) in cocompact _, 2 * R ≤ ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  apply squeeze_zero_norm' ?_ (by simpa using ht.mul_const (∫ y, |f y|))
  filter_upwards [hev] with x hx
  exact newtonianPotential_far_bound hm f (hf.integrable_of_hasCompactSupport hfc) hR hsupport x hx

theorem poissonPotential_tendsto_zero {m : ℕ} (hm : 3 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (poissonPotential f) (cocompact (EuclideanSpace ℝ (Fin m))) (𝓝 0) := by
  change Tendsto (fun x => (poissonNormalization m)⁻¹ * newtonianPotential f x) _ _
  simpa only [mul_zero] using
    (newtonianPotential_tendsto_zero hm f hf hfc).const_mul (poissonNormalization m)⁻¹

end OAI.Analysis.PDE.Schauder
