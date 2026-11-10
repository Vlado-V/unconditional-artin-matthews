module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderApprox
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Standard mollifications are Cauchy simultaneously in C⁰, C^β and L¹. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem smoothData_pairwise_bounds {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α β : ℝ} (hH : 0 ≤ H) (hβ : 0 < β) (hβα : β < α)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∃ r : ℕ → ℝ, (∀ k, 0 ≤ r k) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ k l,
      (∀ x y, |(smoothData (standardMollifier m k) f x - smoothData (standardMollifier m l) f x) -
        (smoothData (standardMollifier m k) f y - smoothData (standardMollifier m l) f y)| ≤
        (r k + r l) * ‖x - y‖ ^ β) ∧
      (∀ x, |smoothData (standardMollifier m k) f x - smoothData (standardMollifier m l) f x| ≤ r k + r l) ∧
      ((∫ x, |smoothData (standardMollifier m k) f x - smoothData (standardMollifier m l) f x|) ≤ r k + r l) := by
  have hα : 0 < α := hβ.trans hβα
  obtain ⟨V, hV, hL1⟩ := standardMollifier_integral_error f hf hfc hH hα.le hh
  let e (k : ℕ) := H * (standardMollifier m k).rOut ^ α
  let a (k : ℕ) := 4 * H * (standardMollifier m k).rOut ^ (α - β)
  let r (k : ℕ) := a k + (1 + V) * e k
  have he0 (k) : 0 ≤ e k := mul_nonneg hH (Real.rpow_nonneg (standardMollifier m k).rOut_pos.le α)
  have ha0 (k) : 0 ≤ a k := mul_nonneg (by positivity) (Real.rpow_nonneg (standardMollifier m k).rOut_pos.le (α - β))
  have he (k) : e k ≤ r k := by dsimp [r]; nlinarith [he0 k, ha0 k, mul_nonneg hV (he0 k)]
  have ha (k) : a k ≤ r k := le_add_of_nonneg_right (mul_nonneg (by linarith) (he0 k))
  have hv (k) : V * e k ≤ r k := by dsimp [r]; nlinarith [he0 k, ha0 k]
  have heT : Tendsto e atTop (𝓝 0) := by
    simpa [e] using ((standardMollifier_radius_tendsto m).rpow_const_nhds_zero hα).const_mul H
  have haT : Tendsto a atTop (𝓝 0) := smoothData_lower_holder_rate_tendsto m hβα
  have hrT : Tendsto r atTop (𝓝 0) := by
    simpa [r] using haT.add (heT.const_mul (1 + V))
  refine ⟨r, fun k => (he0 k).trans (he k), hrT, ?_⟩
  intro k l
  let d (k : ℕ) (x : EuclideanSpace ℝ (Fin m)) := smoothData (standardMollifier m k) f x - f x
  have hd (k x) : |d k x| ≤ e k := smoothData_error _ f hf hH hα.le hh x
  have hdh (k x y) : |d k x - d k y| ≤ a k * ‖x - y‖ ^ β :=
    smoothData_lower_holder_error _ f hf hβ hβα.le hH hh x y
  have hdiff (x) : smoothData (standardMollifier m k) f x - smoothData (standardMollifier m l) f x = d k x - d l x := by
    dsimp [d]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [hdiff x, hdiff y]
    have hid : (d k x - d l x) - (d k y - d l y) = (d k x - d k y) - (d l x - d l y) := by ring
    rw [hid]
    calc
      _ ≤ |d k x - d k y| + |d l x - d l y| := abs_sub _ _
      _ ≤ a k * ‖x - y‖ ^ β + a l * ‖x - y‖ ^ β := add_le_add (hdh k x y) (hdh l x y)
      _ ≤ (r k + r l) * ‖x - y‖ ^ β := by
        have hn := Real.rpow_nonneg (norm_nonneg (x - y)) β
        nlinarith [mul_le_mul_of_nonneg_right (ha k) hn, mul_le_mul_of_nonneg_right (ha l) hn]
  · intro x
    rw [hdiff x]
    exact (abs_sub _ _).trans ((add_le_add (hd k x) (hd l x)).trans (add_le_add (he k) (he l)))
  · have hdi (k) : Integrable (fun x => |d k x|) :=
      (((contDiff_smoothData _ f hf).continuous.sub hf).integrable_of_hasCompactSupport
        ((hasCompactSupport_smoothData _ f hfc).sub hfc)).norm
    have hdiffi : Integrable (fun x => |d k x - d l x|) :=
      (((contDiff_smoothData (standardMollifier m k) f hf).continuous.sub
        (contDiff_smoothData (standardMollifier m l) f hf).continuous).integrable_of_hasCompactSupport
        ((hasCompactSupport_smoothData _ f hfc).sub (hasCompactSupport_smoothData _ f hfc))).norm.congr
          (Filter.Eventually.of_forall (fun x => by
            change |smoothData (standardMollifier m k) f x - smoothData (standardMollifier m l) f x| = |d k x - d l x|
            rw [hdiff x]))
    simp_rw [hdiff]
    calc
      _ ≤ ∫ x, |d k x| + |d l x| := integral_mono hdiffi ((hdi k).add (hdi l)) (fun x => abs_sub _ _)
      _ = (∫ x, |d k x|) + ∫ x, |d l x| := integral_add (hdi k) (hdi l)
      _ ≤ V * e k + V * e l := add_le_add (hL1 k) (hL1 l)
      _ ≤ r k + r l := add_le_add (hv k) (hv l)

end OAI.Analysis.PDE.Schauder
