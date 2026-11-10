module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Field.Basic
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

/-! # Ball Image -/

namespace OAI.RepresentationTheory.Weil.Local.BallImage.Construction

noncomputable section

/-! A local image lemma that turns an exact norm identity into an exact image of small balls. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

theorem small_ball_image_of_norm_identity
    {k : Type*} [NormedField k] (f : k → k) (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (hf : Filter.map f (𝓝 (0 : k)) = 𝓝 (0 : k))
    (hnorm : ∀ x : k, ‖x‖ < ε → ‖f x‖ = d * ‖x‖) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ ε ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f '' Metric.ball (0 : k) r = Metric.ball 0 (d * r) := by
  have himage : f '' Metric.ball (0 : k) ε ∈ 𝓝 (0 : k) := by
    rw [← hf]
    exact Filter.image_mem_map (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp himage
  let r₀ := min ε (δ / d)
  have hr₀ : 0 < r₀ := lt_min hε (div_pos hδ hd)
  refine ⟨r₀, hr₀, min_le_left _ _, ?_⟩
  intro r hr hrr
  have hre : r ≤ ε := hrr.trans (min_le_left _ _)
  have hrd : d * r ≤ δ := by
    have hh := hrr.trans (min_le_right ε (δ / d))
    exact (mul_comm d r).trans_le ((le_div_iff₀ hd).mp hh)
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < r := by simpa using hx
    simpa only [Metric.mem_ball, dist_zero_right, hnorm x (hx'.trans_le hre)] using
      (mul_lt_mul_of_pos_left hx' hd)
  · intro hy
    have hy' : ‖y‖ < d * r := by simpa using hy
    obtain ⟨x, hx, hxy⟩ := hsub (show y ∈ Metric.ball 0 δ from by simpa using hy'.trans_le hrd)
    have hx' : ‖x‖ < ε := by simpa using hx
    refine ⟨x, ?_, hxy⟩
    have hn := hnorm x hx'
    rw [hxy] at hn
    have hlt : ‖x‖ < r := (mul_lt_mul_iff_right₀ hd).mp (by simpa [← hn] using hy')
    simpa using hlt

end

end OAI.RepresentationTheory.Weil.Local.BallImage.Construction
