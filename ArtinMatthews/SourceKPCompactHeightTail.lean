module

public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
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

/-! A square-integrable function has vanishing mass above the compact height exhaustion. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactHeightTail_tendsto (w : Y → ℂ) (hw : MemLp w 2 μY) :
    Tendsto (fun n : ℕ => ∫ y in {y | (n : ℝ) < HY y}, ‖w y‖^2 ∂μY) atTop (𝓝 0) := by
  let S (n : ℕ) : Set Y := {y | (n : ℝ) < HY y}
  let F (n : ℕ) : Y → ℝ := (S n).indicator (fun y => ‖w y‖^2)
  have hS (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_lt measurable_const
      (sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ).measurable
  have hI : Integrable (fun y => ‖w y‖^2) μY := hw.integrable_norm_pow (by norm_num)
  have h : Tendsto (fun n => ∫ y, F n y ∂μY) atTop (𝓝 (∫ _y : Y, (0 : ℝ) ∂μY)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖w y‖^2)
    · exact Eventually.of_forall fun n => hI.aestronglyMeasurable.indicator (hS n)
    · exact Eventually.of_forall fun n => Eventually.of_forall fun y => by
        by_cases hy : y ∈ S n
        · rw [show F n y = ‖w y‖^2 from Set.indicator_of_mem hy _,Real.norm_of_nonneg (sq_nonneg _)]
        · rw [show F n y = 0 from Set.indicator_of_notMem hy _,norm_zero]
          exact sq_nonneg _
    · exact hI
    · exact Eventually.of_forall fun y => by
        obtain ⟨N,hN⟩ := exists_nat_gt (HY y)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        exact (Set.indicator_of_notMem (show y ∉ S n from not_lt.mpr
          (hN.le.trans (Nat.cast_le.mpr hn))) _).symm
  have he : (fun n => ∫ y, F n y ∂μY) =
      fun n : ℕ => ∫ y in S n, ‖w y‖^2 ∂μY := funext fun n => integral_indicator (hS n)
  rw [he,integral_zero] at h
  exact h

end
end ArtinMatthews
