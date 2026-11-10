module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Field.Ultra
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

/-! # Nonarchimedean Norm -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm.Construction

noncomputable section

/-! A nondiscrete nonarchimedean field topology forces its multiplicative norm to be ultrametric. -/

open scoped _root_.Topology

theorem nonarchimedean_norm_ultrametric
    (k : Type) [NormedField k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) : IsUltrametricDist k := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hNondiscrete hd).elim
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    (Metric.ball (0 : k) 1) (Metric.ball_mem_nhds _ zero_lt_one)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds U.zero_mem)
  obtain ⟨u, hu, huε⟩ := NormedField.exists_norm_lt k hε
  have huU : u ∈ U := hεU (by simpa using huε)
  apply isUltrametricDist_iff_forall_norm_natCast_le_one.mpr
  intro n
  by_contra! hn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ‖u‖) hn
  have hbound := hU (U.nsmul_mem huU (n ^ m))
  rw [Metric.mem_ball, dist_zero_right, nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow] at hbound
  exact lt_asymm ((div_lt_iff₀ hu).mp hm) hbound

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm.Construction
