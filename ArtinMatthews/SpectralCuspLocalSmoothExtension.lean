module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! A local two-cell smooth section has a global smooth extension near an
interior period at any fixed height.  No global smooth representative is
assumed. -/

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace ArtinMatthews

def spectralOpenTwoCell (N Y : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < 2 * N ∧ Y < p.2}

theorem spectralOpenTwoCell_isOpen (N Y : ℝ) : IsOpen (spectralOpenTwoCell N Y) :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_const continuous_snd))

theorem spectral_local_cutoff_contDiff (S : Set (ℝ × ℝ)) (hS : IsOpen S)
    (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u S)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : tsupport φ ⊆ S) :
    ContDiff ℝ ∞ (fun p => φ p • u p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport φ
  · exact hφ.contDiffAt.smul (hu.contDiffAt (hS.mem_nhds (hsupp hp)))
  · have he : φ =ᶠ[𝓝 p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hp
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    simp only [hq, zero_smul]

theorem spectralLocalTwoCell_smooth_extension_uniform (N Y y₀ : ℝ) (hN : 0 < N) (hy₀ : Y < y₀)
    (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y)) :
    ∃ G : ℝ × ℝ → ℂ, ContDiff ℝ ∞ G ∧
      ∀ y, |y - y₀| < (y₀ - Y) / 4 →
        ∀ x ∈ Icc (N / 2) (3 * N / 2), G =ᶠ[𝓝 (x, y)] u := by
  let bx : ContDiffBump N := ⟨3 * N / 4, 7 * N / 8, by positivity, by linarith⟩
  let by₀ : ContDiffBump y₀ :=
    ⟨(y₀ - Y) / 4, (y₀ - Y) / 2, by linarith, by linarith⟩
  let φ : ℝ × ℝ → ℝ := fun p => bx p.1 * by₀ p.2
  let K : Set (ℝ × ℝ) :=
    (Prod.fst ⁻¹' closedBall N bx.rOut) ∩ (Prod.snd ⁻¹' closedBall y₀ by₀.rOut)
  have hKclosed : IsClosed K :=
    (isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_closedBall.preimage continuous_snd)
  have hsupport : Function.support φ ⊆ K := by
    intro p hp
    have hmul : bx p.1 * by₀ p.2 ≠ 0 := hp
    have hx : p.1 ∈ tsupport bx := subset_tsupport _ (mul_ne_zero_iff.mp hmul).1
    have hy : p.2 ∈ tsupport by₀ := subset_tsupport _ (mul_ne_zero_iff.mp hmul).2
    rw [bx.tsupport_eq] at hx
    rw [by₀.tsupport_eq] at hy
    exact ⟨hx, hy⟩
  have hKS : K ⊆ spectralOpenTwoCell N Y := by
    intro p hp
    have hx : |p.1 - N| ≤ 7 * N / 8 := by simpa only [K, mem_inter_iff, mem_preimage,
      mem_closedBall, Real.dist_eq, bx] using hp.1
    have hy : |p.2 - y₀| ≤ (y₀ - Y) / 2 := by simpa only [K, mem_inter_iff, mem_preimage,
      mem_closedBall, Real.dist_eq, by₀] using hp.2
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    change 0 < p.1 ∧ p.1 < 2 * N ∧ Y < p.2
    constructor
    · linarith
    · constructor <;> linarith
  have hsupp : tsupport φ ⊆ spectralOpenTwoCell N Y :=
    (closure_minimal hsupport hKclosed).trans hKS
  have hφ : ContDiff ℝ ∞ φ :=
    (bx.contDiff.comp contDiff_fst).mul (by₀.contDiff.comp contDiff_snd)
  refine ⟨fun p => φ p • u p,
    spectral_local_cutoff_contDiff _ (spectralOpenTwoCell_isOpen N Y) u hu φ hφ hsupp, ?_⟩
  intro y hy x hx
  have hxball : x ∈ ball N bx.rIn := by
    change |x - N| < 3 * N / 4
    apply abs_lt.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hyball : y ∈ ball y₀ by₀.rIn := by
    simpa only [mem_ball, Real.dist_eq, by₀] using hy
  have hnb : (Prod.fst ⁻¹' ball N bx.rIn) ∩ (Prod.snd ⁻¹' ball y₀ by₀.rIn) ∈ 𝓝 (x, y) :=
    ((isOpen_ball.preimage continuous_fst).inter
      (isOpen_ball.preimage continuous_snd)).mem_nhds ⟨hxball, hyball⟩
  filter_upwards [hnb] with p hp
  have hpx : bx p.1 = 1 := bx.one_of_mem_closedBall (ball_subset_closedBall hp.1)
  have hpy : by₀ p.2 = 1 := by₀.one_of_mem_closedBall (ball_subset_closedBall hp.2)
  simp only [φ, hpx, hpy, one_mul, one_smul]

theorem spectralLocalTwoCell_smooth_extension (N Y y₀ : ℝ) (hN : 0 < N) (hy₀ : Y < y₀)
    (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y)) :
    ∃ G : ℝ × ℝ → ℂ, ContDiff ℝ ∞ G ∧
      ∀ x ∈ Icc (N / 2) (3 * N / 2), G =ᶠ[𝓝 (x, y₀)] u := by
  obtain ⟨G,hG,he⟩ := spectralLocalTwoCell_smooth_extension_uniform N Y y₀ hN hy₀ u hu
  refine ⟨G,hG,he y₀ ?_⟩
  simpa only [sub_self, abs_zero] using (show 0 < (y₀ - Y) / 4 by linarith)

end ArtinMatthews
