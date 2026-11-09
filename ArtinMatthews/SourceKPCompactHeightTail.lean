module

public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


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
