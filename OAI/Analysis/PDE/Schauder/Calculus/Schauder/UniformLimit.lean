module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform completeness in a quantitative form suitable for Newtonian derivative limits. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem clm_apply_tendsto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℕ → E →L[ℝ] F} {g : E →L[ℝ] F}
    (hf : Tendsto f atTop (𝓝 g)) (v : E) :
    Tendsto (fun k => f k v) atTop (𝓝 (g v)) :=
  ((ContinuousLinearMap.apply ℝ F v).continuous.tendsto g).comp hf

theorem norm_sub_tendsto {F : Type*} [NormedAddCommGroup F]
    {f g : ℕ → F} {a b : F}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
    Tendsto (fun k => ‖f k - g k‖) atTop (𝓝 ‖a - b‖) := (hf.sub hg).norm

theorem exists_uniform_limit_of_pairwise_bound {X F : Type*}
    [NormedAddCommGroup F] [CompleteSpace F]
    (f : ℕ → X → F) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hb : ∀ k l x, ‖f k x - f l x‖ ≤ r k + r l) :
    ∃ g : X → F, (∀ k x, ‖f k x - g x‖ ≤ r k) ∧ TendstoUniformly f g atTop := by
  have hc (x : X) : CauchySeq (fun k => f k x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually (Iio_mem_nhds (half_pos hε)))
    refine ⟨N, fun k hk l hl => ?_⟩
    rw [dist_eq_norm]
    exact (hb k l x).trans_lt (by linarith [hN k hk, hN l hl])
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hc x)
  have hbg (k : ℕ) (x : X) : ‖f k x - g x‖ ≤ r k := by
    have ht := (((hg x).const_sub (f k x)).norm).sub (hr.const_add (r k))
    have ht' : Tendsto (fun l => ‖f k x - f l x‖ - (r k + r l)) atTop (𝓝 (‖f k x - g x‖ - r k)) := by
      simpa using ht
    have h := le_of_tendsto ht' (Filter.Eventually.of_forall (fun l => sub_nonpos.mpr (hb k l x)))
    linarith
  refine ⟨g, hbg, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hr.eventually (Iio_mem_nhds hε)] with k hk
  intro x
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbg k x).trans_lt hk

end OAI.Analysis.PDE.Schauder
