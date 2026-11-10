module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
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

/-! # Norm Small Subgroup -/

namespace OAI.RepresentationTheory.Weil.Local.NormSmallSubgroup.Construction

noncomputable section

/-! Small open subgroups of the compact quadratic norm-one group. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {k : Type*} [NormedField k] [IsUltrametricDist k]

def normSmallSubgroup (h : ¬ ∃ t : k, t ^ 2 = -1)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : Subgroup (QuadraticNormAt.Construction.QuadraticNormOne k) where
  carrier := {p | ∃ t : k, ‖t‖ < r ∧ QuadraticNormAt.Construction.quadraticNormChart h t = p}
  one_mem' := ⟨0, by simpa using hr, QuadraticNormAt.Construction.quadraticNormChart_zero h⟩
  mul_mem' := by
    rintro p q ⟨t, ht, rfl⟩ ⟨u, hu, rfl⟩
    have hn := NormChartOperations.Construction.one_sub_mul_norm_eq_one t u (ht.trans_le hr1) (hu.trans_le hr1)
    have hd : 1 - t * u ≠ 0 := by intro he; simp [he] at hn
    refine ⟨(t + u) / (1 - t * u), ?_, (NormChartOperations.Construction.quadraticNormChart_mul h t u hd).symm⟩
    exact (NormChartOperations.Construction.norm_normChart_product_coordinate_le t u (ht.trans_le hr1) (hu.trans_le hr1)).trans_lt
      (max_lt ht hu)
  inv_mem' := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨-t, by simpa only [norm_neg] using ht, (NormChartOperations.Construction.quadraticNormChart_inv h t).symm⟩

theorem mem_normSmallSubgroup_iff [CharZero k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (p : QuadraticNormAt.Construction.QuadraticNormOne k) :
    p ∈ normSmallSubgroup h r hr hr1 ↔
      p ≠ QuadraticNormAt.Construction.QuadraticNormOne.minusOne ∧ ‖QuadraticNormAt.Construction.quadraticNormCoordinate p‖ < r := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨QuadraticNormAt.Construction.quadraticNormChart_ne_minusOne h t, by simpa only [QuadraticNormAt.Construction.quadraticNormCoordinate_chart] using ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨QuadraticNormAt.Construction.quadraticNormCoordinate p, ht, QuadraticNormAt.Construction.quadraticNormChart_coordinate h p hp⟩

theorem normSmallSubgroup_isOpen [CharZero k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    IsOpen (normSmallSubgroup h r hr hr1 : Set (QuadraticNormAt.Construction.QuadraticNormOne k)) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨hpne, hpn⟩ := (mem_normSmallSubgroup_iff h r hr hr1 p).mp hp
  have hne : {q : QuadraticNormAt.Construction.QuadraticNormOne k | q ≠ QuadraticNormAt.Construction.QuadraticNormOne.minusOne} ∈ 𝓝 p :=
    isOpen_ne.mem_nhds hpne
  have hnorm : {q : QuadraticNormAt.Construction.QuadraticNormOne k | ‖QuadraticNormAt.Construction.quadraticNormCoordinate q‖ < r} ∈ 𝓝 p :=
    (QuadraticNormAt.Construction.quadraticNormCoordinate_continuousAt p hpne).norm.preimage_mem_nhds
      (isOpen_Iio.mem_nhds hpn)
  exact Filter.mem_of_superset (Filter.inter_mem hne hnorm) fun q hq =>
    (mem_normSmallSubgroup_iff h r hr hr1 q).mpr hq

theorem normSmallSubgroup_no_two_torsion [CharZero k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (p : QuadraticNormAt.Construction.QuadraticNormOne k) (hp : p ∈ normSmallSubgroup h r hr hr1) (hp2 : p ^ 2 = 1) : p = 1 := by
  rcases (QuadraticNormAt.Construction.QuadraticNormOne.sq_eq_one_iff p).mp hp2 with hp1 | hpm
  · exact hp1
  · exact ((mem_normSmallSubgroup_iff h r hr hr1 p).mp hp).1 hpm |>.elim

def normSmallChart [CharZero k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Metric.ball (0 : k) r ≃ normSmallSubgroup h r hr hr1 where
  toFun t := ⟨QuadraticNormAt.Construction.quadraticNormChart h t.val, t.val,
    by simpa only [Metric.mem_ball, dist_zero_right] using t.property, rfl⟩
  invFun p := ⟨QuadraticNormAt.Construction.quadraticNormCoordinate p.val, by
    simpa only [Metric.mem_ball, dist_zero_right] using
      ((mem_normSmallSubgroup_iff h r hr hr1 p.val).mp p.property).2⟩
  left_inv t := by apply Subtype.ext; exact QuadraticNormAt.Construction.quadraticNormCoordinate_chart h t.val
  right_inv p := by
    apply Subtype.ext
    exact QuadraticNormAt.Construction.quadraticNormChart_coordinate h p.val
      ((mem_normSmallSubgroup_iff h r hr hr1 p.val).mp p.property).1

end

end OAI.RepresentationTheory.Weil.Local.NormSmallSubgroup.Construction
