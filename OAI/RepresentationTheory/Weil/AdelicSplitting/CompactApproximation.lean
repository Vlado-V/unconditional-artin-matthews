module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # Compact Approximation -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CompactApproximation.LocalAnalysis

noncomputable section

/-! Compact indicators are approximated by compact open neighborhoods in
every finite Lᵖ norm. This applies to the arbitrary reference compact set
in the prescribed Haar normalization. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ENNReal

variable {E : Type*} [MetricSpace E] [ProperSpace E] [IsUltrametricDist E]

def compactNeighborhood (S : Set E) (j : ℕ) : Set E :=
  Metric.cthickening ((j : ℝ) + 1)⁻¹ S

omit [ProperSpace E] in
theorem compactNeighborhood_clopen {S : Set E} (hS : IsCompact S) (j : ℕ) :
    IsClopen (compactNeighborhood S j) := by
  refine ⟨Metric.isClosed_cthickening, ?_⟩
  rw [compactNeighborhood, hS.cthickening_eq_biUnion_closedBall (by positivity)]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ =>
    IsUltrametricDist.isOpen_closedBall x (by positivity)

omit [IsUltrametricDist E] in
theorem compactNeighborhood_compact {S : Set E} (hS : IsCompact S) (j : ℕ) :
    IsCompact (compactNeighborhood S j) := hS.cthickening

omit [ProperSpace E] [IsUltrametricDist E] in
theorem subset_compactNeighborhood (S : Set E) (j : ℕ) : S ⊆ compactNeighborhood S j :=
  Metric.self_subset_cthickening S

omit [ProperSpace E] [IsUltrametricDist E] in
theorem compactNeighborhood_antitone (S : Set E) : Antitone (compactNeighborhood S) := by
  intro i j hij
  apply Metric.cthickening_mono
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  exact_mod_cast Nat.add_le_add_right hij 1

omit [ProperSpace E] [IsUltrametricDist E] in
theorem iInter_compactNeighborhood {S : Set E} (hS : IsClosed S) :
    (⋂ j, compactNeighborhood S j) = S := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← hS.closure_eq, Metric.closure_eq_iInter_cthickening]
    apply Set.mem_iInter.mpr
    intro ε
    apply Set.mem_iInter.mpr
    intro hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    apply Metric.cthickening_mono (by simpa only [one_div] using hj.le) S
    exact Set.mem_iInter.mp hx j
  · exact Set.subset_iInter (subset_compactNeighborhood S)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

theorem compactNeighborhood_sdiff_measure_tendsto {S : Set E} (hS : IsCompact S) :
    Tendsto (fun j => μ (compactNeighborhood S j \ S)) atTop (𝓝 0) := by
  have hi : (⋂ j, compactNeighborhood S j \ S) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    intro hx
    have hxS : x ∈ S := by
      rw [← iInter_compactNeighborhood hS.isClosed]
      exact Set.mem_iInter.mpr (fun j => (hx j).1)
    exact (hx 0).2 hxS
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun j => ((compactNeighborhood_clopen hS j).isOpen.measurableSet.diff
      hS.measurableSet).nullMeasurableSet)
    (fun i j hij => Set.sdiff_subset_sdiff_left (compactNeighborhood_antitone S hij))
    ⟨0, (measure_mono Set.sdiff_subset).trans_lt
      (compactNeighborhood_compact hS 0).measure_lt_top |>.ne⟩
  simpa only [hi, measure_empty, Function.comp_def] using h

omit [ProperSpace E] [IsUltrametricDist E] [MeasurableSpace E] [BorelSpace E] in
theorem compactNeighborhood_indicator_sub {S : Set E} (_hS : IsCompact S) (j : ℕ) :
    (fun x => (compactNeighborhood S j).indicator (fun _ => (1 : ℂ)) x -
      S.indicator (fun _ => (1 : ℂ)) x) =
      (compactNeighborhood S j \ S).indicator (fun _ => (1 : ℂ)) := by
  funext x
  by_cases hx : x ∈ S
  · simp [hx, subset_compactNeighborhood S j hx]
  · by_cases hV : x ∈ compactNeighborhood S j <;> simp [hx, hV]

theorem compactNeighborhood_indicator_eLpNorm_tendsto {S : Set E} (hS : IsCompact S)
    (p : ℝ≥0∞) (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    Tendsto (fun j => eLpNorm
      (fun x => (compactNeighborhood S j).indicator (fun _ => (1 : ℂ)) x -
        S.indicator (fun _ => (1 : ℂ)) x) p μ) atTop (𝓝 0) := by
  simp only [compactNeighborhood_indicator_sub hS]
  have he (j : ℕ) : eLpNorm
      ((compactNeighborhood S j \ S).indicator (fun _ => (1 : ℂ))) p μ =
      μ (compactNeighborhood S j \ S) ^ (1 / p.toReal) := by
    rw [eLpNorm_indicator_const
      ((compactNeighborhood_clopen hS j).isOpen.measurableSet.diff hS.measurableSet).nullMeasurableSet hp hpfin]
    simp
  simp only [he]
  have h := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).continuousAt.tendsto.comp
    (compactNeighborhood_sdiff_measure_tendsto μ hS)
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos
    (one_div_pos.mpr (ENNReal.toReal_pos hp hpfin))] using! h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CompactApproximation.LocalAnalysis
