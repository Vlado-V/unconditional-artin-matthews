module

public import ArtinMatthews.VaryingKummerAnalyticIdealCharacterTheta
public import ArtinMatthews.VaryingKummerAnalyticMixedIntegralIdeal
public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverage
public import ArtinMatthews.VaryingKummerAnalyticPeriodicThetaGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Subquadratic growth of the actual periodic theta average in arbitrary
signature, using the compact Dirichlet-unit domain and actual tail estimates. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedPeriodicTheta_boundedAverage_hasSubquadraticGrowth
    (B : EuclideanSpace ℝ (MixedIdealIndex K J) ≃L[ℝ] EuclideanSpace ℝ (MixedIdealIndex K J))
    (N : ℕ) [NeZero N] (w : (MixedIdealIndex K J → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    {S : Set (logSpace K)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    HasSubquadraticGrowth (mellin (fun t => ∫ u in S,
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
  have H := averagedNormalizedPeriodicTheta_mellin_hasSubquadraticGrowth μ F N w hzero hsum
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
