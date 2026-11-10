module

public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.L2MeasurableCutoff
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Literal height-sublevel restriction of the scalar Haar mass. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => SourceKPCompactFormCore K hζ
local notation "V" => SourceKPCompactH1 K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L" => Lp ℂ 2 μ
local notation "S" => (fun R : ℝ => Set.ofPred (fun y : Y => sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ R))

def sourceKPCompactHeightCutoff (R : ℝ) : L →L[ℂ] L :=
  measurableL2Cutoff μ (S R)
    (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R).measurableSet

def sourceKPCompactH1LocalizedMass (R : ℝ) : V →L[ℂ] L :=
  (sourceKPCompactHeightCutoff K hζ R).comp (sourceKPCompactH1Mass K hζ)

theorem sourceKPCompactH1LocalizedMass_coe (R : ℝ) (u : V) :
    (sourceKPCompactH1LocalizedMass K hζ R u : Y → ℂ) =ᵐ[μ]
      (S R).indicator (sourceKPCompactH1Mass K hζ u) :=
  measurableL2Cutoff_coe μ (S R)
    (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R).measurableSet
    (sourceKPCompactH1Mass K hζ u)

theorem sourceKPCompactH1LocalizedMass_norm_sq (R : ℝ) (u : V) :
    ‖sourceKPCompactH1LocalizedMass K hζ R u‖ ^ 2 =
      ∫ y in S R, ‖sourceKPCompactH1Mass K hζ u y‖ ^ 2 ∂μ :=
  measurableL2Cutoff_norm_sq μ (S R)
    (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R).measurableSet
    (sourceKPCompactH1Mass K hζ u)

theorem sourceKPCompactH1LocalizedMass_core (R : ℝ) (f : T) :
    sourceKPCompactH1LocalizedMass K hζ R (sourceKPCompactH1Core K hζ f) =
      sourceKPCompactHeightCutoff K hζ R (sourceKPCompactFormCoreMass K hζ f) :=
  congrArg (sourceKPCompactHeightCutoff K hζ R) (sourceKPCompactH1Mass_core K hζ f)

theorem sourceKPCompactH1LocalizedMass_compact_of_core (R : ℝ)
    (hcore : IsCompact (closure
      ((sourceKPCompactHeightCutoff K hζ R).comp (sourceKPCompactFormCoreMass K hζ) ''
        Metric.closedBall (0 : T) 2))) :
    IsCompactOperator (sourceKPCompactH1LocalizedMass K hζ R) := by
  let F := sourceKPCompactH1LocalizedMass K hζ R
  let e := sourceKPCompactH1Core K hζ
  let A := Metric.closedBall (0 : T) 2
  have hball : Metric.closedBall (0 : V) 1 ⊆ closure (e '' A) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp (sourceKPCompactH1Core_denseRange K hζ)
      u (min ε 1) (lt_min hε zero_lt_one)
    have hd : ‖e f - u‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact hf.trans_le (min_le_right _ _)
    have hfA : f ∈ A := by
      change f ∈ Metric.closedBall (0 : T) 2
      rw [Metric.mem_closedBall, dist_zero_right, ← e.norm_map]
      calc
        ‖e f‖ = ‖e f - u + u‖ := by rw [sub_add_cancel]
        _ ≤ ‖e f - u‖ + ‖u‖ := norm_add_le _ _
        _ ≤ 2 := by linarith
    exact ⟨e f, mem_image_of_mem e hfA, hf.trans_le (min_le_left _ _)⟩
  have himage : F '' (e '' A) =
      (sourceKPCompactHeightCutoff K hζ R).comp (sourceKPCompactFormCoreMass K hζ) '' A := by
    rw [image_image]
    exact congrArg (fun g : T → L => g '' A)
      (funext (sourceKPCompactH1LocalizedMass_core K hζ R))
  have hsub : F '' Metric.closedBall (0 : V) 1 ⊆ closure (F '' (e '' A)) :=
    (image_mono hball).trans (image_closure_subset_closure_image F.continuous)
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall F.toLinearMap zero_lt_one).mpr
  exact hcore.of_isClosed_subset isClosed_closure (closure_minimal (himage ▸ hsub) isClosed_closure)

end
end ArtinMatthews
