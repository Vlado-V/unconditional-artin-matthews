module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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

/-! Uniform compact support and L¹ approximation for the standard mollifiers. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology Convolution Pointwise
namespace OAI.Analysis.PDE.Schauder

theorem support_smoothData_subset_ball {m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) {R : ℝ}
    (hf : Function.support f ⊆ ball 0 R) :
    Function.support (smoothData φ f) ⊆ ball 0 (φ.rOut + R) := by
  intro x hx
  have hs := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hx
  change x ∈ Function.support (φ.normed volume) + Function.support f at hs
  obtain ⟨y, hy, z, hz, rfl⟩ := hs
  rw [φ.support_normed_eq] at hy
  have hy' : ‖y‖ < φ.rOut := by simpa using hy
  have hz' : ‖z‖ < R := by simpa using hf hz
  simpa using (norm_add_le y z).trans_lt (add_lt_add hy' hz')

theorem standardMollifier_support_uniform {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hfc : HasCompactSupport f) :
    ∃ R > 0, Function.support f ⊆ ball 0 R ∧
      ∀ k, Function.support (smoothData (standardMollifier m k) f) ⊆ ball 0 R := by
  obtain ⟨R, hR, hs⟩ := hfc.isCompact.isBounded.subset_ball_lt 0 0
  have hf : Function.support f ⊆ ball 0 R := subset_closure.trans hs
  refine ⟨1 + R, by linarith, hf.trans (ball_subset_ball (by linarith)), ?_⟩
  intro k
  have hk : (standardMollifier m k).rOut ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact (support_smoothData_subset_ball _ f hf).trans (ball_subset_ball (by linarith))

theorem integral_abs_le_of_support_ball {m : ℕ}
    (g : EuclideanSpace ℝ (Fin m) → ℝ) {R U : ℝ}
    (hs : Function.support g ⊆ ball 0 R) (hb : ∀ x, |g x| ≤ U) :
    (∫ x, |g x|) ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) R) * U := by
  have he : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) R, |g x|) = ∫ x, |g x| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hg : g x = 0 := by
      by_contra hg
      exact hx (hs hg)
    simp [hg]
  have h := norm_setIntegral_le_of_norm_le_const (f := fun x => |g x|) (C := U)
    (measure_ball_lt_top : volume (ball (0 : EuclideanSpace ℝ (Fin m)) R) < ⊤)
    (fun x (_ : x ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R) => by simpa using hb x)
  rw [he] at h
  have hi0 : 0 ≤ ∫ x, |g x| := integral_nonneg (fun x => abs_nonneg (g x))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hi0, mul_comm] using h

theorem standardMollifier_integral_error {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∃ V ≥ 0, ∀ k, (∫ x, |smoothData (standardMollifier m k) f x - f x|) ≤
      V * (H * (standardMollifier m k).rOut ^ α) := by
  obtain ⟨R, hR, hs, hsk⟩ := standardMollifier_support_uniform f hfc
  refine ⟨volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) R), ENNReal.toReal_nonneg, ?_⟩
  intro k
  apply integral_abs_le_of_support_ball _ _ (smoothData_error _ f hf hH hα hh)
  intro x hx
  by_contra h
  have h1 : smoothData (standardMollifier m k) f x = 0 := by
    by_contra h1
    exact h (hsk k h1)
  have h2 : f x = 0 := by
    by_contra h2
    exact h (hs h2)
  exact hx (by simp [h1, h2])

end OAI.Analysis.PDE.Schauder
