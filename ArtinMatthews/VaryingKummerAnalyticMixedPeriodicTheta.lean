module

public import ArtinMatthews.VaryingKummerAnalyticMixedLogCoordinates
public import ArtinMatthews.VaryingKummerAnalyticPeriodicTheta
public import ArtinMatthews.VaryingKummerAnalyticThetaAverages
public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverage
public import ArtinMatthews.VaryingKummerAnalyticPeriodicThetaAverages
public import ArtinMatthews.VaryingKummerAnalyticThetaDualAverages
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

/-! Entire Mellin transforms of the actual residue-weighted mixed ideal
theta averages. The finite residue character cancels both constant modes;
the full real/complex signature and actual unit-log domain are retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedPeriodicTheta_boundedAverage_entire
    (B : EuclideanSpace ℝ (MixedIdealIndex K J) ≃L[ℝ] EuclideanSpace ℝ (MixedIdealIndex K J))
    (N : ℕ) [NeZero N] (w : (MixedIdealIndex K J → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    {S : Set (logSpace K)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S,
      normalizedPeriodicTheta (logScaledLattice B (mixedIdealLogScale K J u)) N w t)) := by
  let μ : Measure S := Measure.comap ((↑) : S → logSpace K) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let u : S → MixedIdealIndex K J → ℝ := fun x => mixedIdealLogScale K J x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((mixedIdealLogScale_continuous K J i).comp continuous_subtype_val).measurable
  obtain ⟨U,hU⟩ := mixedIdealLogScale_abs_bound K J hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖*Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖*Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl,adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply,neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : ∀ z, Measurable (fun x => F x (euclideanInteger z)) :=
    fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z)
  have HN : ∀ z, Measurable (fun x => adjointEquiv (F x).symm (euclideanInteger z)) := by
    intro z
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from fun x => adjointEquiv_logScaledLattice B (u x)]
    exact logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z)
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹|:ℝ):ℂ) =
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) := by
    intro x
    dsimp only [F,u]
    rw [logScaledLattice_det,mixedIdealLogScale_sum,Real.exp_zero,one_mul]
  have H := averagedNormalizedPeriodicTheta_mellin_entire μ F N w hzero hsum
    R T hR hT HB HD HM HN _ HC
  have HE : averagedNormalizedPeriodicTheta μ F N w =
      (fun t => ∫ u in S, normalizedPeriodicTheta (logScaledLattice B (mixedIdealLogScale K J u)) N w t) := by
    funext t
    exact integral_subtype_comap hS
      (fun u => normalizedPeriodicTheta (logScaledLattice B (mixedIdealLogScale K J u)) N w t)
  rw [HE] at H
  exact H


end
end ArtinMatthews.VaryingKummerAnalytic
