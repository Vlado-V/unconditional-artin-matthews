module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.NormSmallSubgroup
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup
public import OAI.RepresentationTheory.Weil.Local.SquareBall
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
public import OAI.RepresentationTheory.Weil.Local.NormChartOperations


set_option backward.privateInPublic true
@[expose] public section

/-! # Norm Square Classes -/

namespace OAI.RepresentationTheory.Weil.Local.NormSquareClasses.Construction

noncomputable section

/-! Squares and square cosets in a small norm-one subgroup. -/

open Set _root_.Metric

variable {k : Type*} [NormedField k] [IsUltrametricDist k] [CharZero k]

theorem normSmall_mem_squares_iff
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (himage : (SquareBall.Construction.normOneSquareCoordinate : k → k) '' Metric.ball 0 r =
      Metric.ball 0 (‖(2 : k)‖ * r))
    (a : NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1) :
    a ∈ QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1) ↔
      ‖QuadraticNormAt.Construction.quadraticNormCoordinate a.val‖ < ‖(2 : k)‖ * r := by
  have hsq (b : NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1) :
      QuadraticNormAt.Construction.quadraticNormCoordinate (b.val ^ 2) = SquareBall.Construction.normOneSquareCoordinate (QuadraticNormAt.Construction.quadraticNormCoordinate b.val) := by
    obtain ⟨t, ht, he⟩ := b.property
    have hn := NormChartOperations.Construction.one_sub_mul_norm_eq_one t t (ht.trans_le hr1) (ht.trans_le hr1)
    have hd : 1 - t ^ 2 ≠ 0 := by
      intro hz
      rw [← pow_two, hz, norm_zero] at hn
      exact zero_ne_one hn
    rw [← he, QuadraticNormAt.Construction.quadraticNormCoordinate_chart, NormChartOperations.Construction.quadraticNormChart_sq h t hd,
      QuadraticNormAt.Construction.quadraticNormCoordinate_chart]
  constructor
  · rintro ⟨b, hb⟩
    have hb' : b.val ^ 2 = a.val := congrArg Subtype.val hb
    have ht : QuadraticNormAt.Construction.quadraticNormCoordinate b.val ∈ Metric.ball (0 : k) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        ((NormSmallSubgroup.Construction.mem_normSmallSubgroup_iff h r hr hr1 b.val).mp b.property).2
    have he : SquareBall.Construction.normOneSquareCoordinate (QuadraticNormAt.Construction.quadraticNormCoordinate b.val) = QuadraticNormAt.Construction.quadraticNormCoordinate a.val := by
      rw [← hsq, hb']
    have hm : QuadraticNormAt.Construction.quadraticNormCoordinate a.val ∈ (SquareBall.Construction.normOneSquareCoordinate : k → k) '' Metric.ball 0 r :=
      ⟨_, ht, he⟩
    rw [himage] at hm
    simpa only [Metric.mem_ball, dist_zero_right] using hm
  · intro ha
    have hm : QuadraticNormAt.Construction.quadraticNormCoordinate a.val ∈ (SquareBall.Construction.normOneSquareCoordinate : k → k) '' Metric.ball 0 r := by
      rw [himage]
      simpa only [Metric.mem_ball, dist_zero_right] using ha
    obtain ⟨t, ht, he⟩ := hm
    have ht' : ‖t‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using ht
    have hn := NormChartOperations.Construction.one_sub_mul_norm_eq_one t t (ht'.trans_le hr1) (ht'.trans_le hr1)
    have hd : 1 - t ^ 2 ≠ 0 := by
      intro hz
      rw [← pow_two, hz, norm_zero] at hn
      exact zero_ne_one hn
    refine ⟨NormSmallSubgroup.Construction.normSmallChart h r hr hr1 ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change QuadraticNormAt.Construction.quadraticNormChart h t ^ 2 = a.val
    rw [NormChartOperations.Construction.quadraticNormChart_sq h t hd, he]
    exact QuadraticNormAt.Construction.quadraticNormChart_coordinate h a.val
      ((NormSmallSubgroup.Construction.mem_normSmallSubgroup_iff h r hr hr1 a.val).mp a.property).1

theorem normSmall_inverse_mul_norm
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (a b : NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1) :
    ‖QuadraticNormAt.Construction.quadraticNormCoordinate (a⁻¹ * b).val‖ =
      ‖QuadraticNormAt.Construction.quadraticNormCoordinate b.val - QuadraticNormAt.Construction.quadraticNormCoordinate a.val‖ := by
  obtain ⟨t, ht, he⟩ := a.property
  obtain ⟨u, hu, he'⟩ := b.property
  have hn := NormChartOperations.Construction.one_sub_mul_norm_eq_one (-t) u (by simpa only [norm_neg] using ht.trans_le hr1)
    (hu.trans_le hr1)
  have hd : 1 - (-t) * u ≠ 0 := by intro hz; rw [hz, norm_zero] at hn; exact zero_ne_one hn
  change ‖QuadraticNormAt.Construction.quadraticNormCoordinate (a.val⁻¹ * b.val)‖ = _
  rw [← he, ← he', QuadraticNormAt.Construction.quadraticNormCoordinate_chart, QuadraticNormAt.Construction.quadraticNormCoordinate_chart,
    NormChartOperations.Construction.quadraticNormChart_inv, NormChartOperations.Construction.quadraticNormChart_mul h (-t) u hd, QuadraticNormAt.Construction.quadraticNormCoordinate_chart,
    norm_div, hn, div_one]
  congr 1
  ring

end

end OAI.RepresentationTheory.Weil.Local.NormSquareClasses.Construction
