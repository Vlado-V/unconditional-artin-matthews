module

public import Mathlib.NumberTheory.LocalField.Basic
public import ArtinMatthews.NativeLocalNorm
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

/-! Analytic topological conditions derived from the actual native local
norm, rather than added to the comparison statement. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory
open scoped Topology Classical ValuativeRel

theorem ultrametric_nonarchimedean (K : Type) [NormedField K] [IsUltrametricDist K] :
    NonarchimedeanAddGroup K where
  toIsTopologicalAddGroup := inferInstance
  is_nonarchimedean := by
    intro s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    refine ⟨IsUltrametricDist.closedBall_openAddSubgroup K (half_pos hε), ?_⟩
    intro x hx
    apply hsub
    change dist x 0 < ε
    rw [dist_zero_right]
    change x ∈ Metric.closedBall 0 (ε / 2) at hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hx.trans_lt (half_lt_self hε)

theorem nontrivialNorm_not_discrete (K : Type) [NontriviallyNormedField K] :
    ¬ DiscreteTopology K := by
  intro hd
  let : DiscreteTopology K := hd
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set K)) 0 (by simp)
  obtain ⟨x, hx, hxε⟩ := NormedField.exists_norm_lt K hε
  have hx0 : x = 0 := hsub (by simpa only [Metric.mem_ball, dist_zero_right] using hxε)
  simp only [hx0, norm_zero, lt_self_iff_false] at hx

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem nativeLocalNorm_nonarchimedean :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    NonarchimedeanAddGroup K := by
  let : NontriviallyNormedField K := localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := nativeLocalNorm_ultrametric K
  exact ultrametric_nonarchimedean K

theorem nativeLocalNorm_not_discrete :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    ¬ DiscreteTopology K := by
  let : NontriviallyNormedField K := localFieldNontriviallyNormedField K
  exact nontrivialNorm_not_discrete K

end

end ArtinMatthews.QuadraticWeil
