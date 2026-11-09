module

public import ArtinMatthews.VaryingKummerAnalyticThetaGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual subquadratic growth of the mixed-signature ideal theta averages and
of the entire completed Dedekind function. The compact unit-domain bounds are
proved for these concrete lattices, with no presumed L-function growth. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedIdealThetaXi_boundedAverage_hasSubquadraticGrowth {S : Set (logSpace K)}
    (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    HasSubquadraticGrowth (fun s => ∫ u in S,
      thetaMellinXi (logScaledLattice (mixedIdealMatrix K I)
        (mixedIdealLogScale K I u)) s) := by
  let μ : Measure S := Measure.comap ((↑) : S → logSpace K) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS, Set.image_univ, Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let B := mixedIdealMatrix K I
  let u : S → MixedIdealIndex K I → ℝ := fun x => mixedIdealLogScale K I x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((mixedIdealLogScale_continuous K I i).comp continuous_subtype_val).measurable
  obtain ⟨U, hU⟩ := mixedIdealLogScale_abs_bound K I hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖ * Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖ * Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl, adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply, neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : StronglyMeasurable (fun p : S × ℝ => normalizedThetaTail (F p.1) p.2) :=
    normalizedThetaTail_joint_stronglyMeasurable (B := F)
      (fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z))
  have HN : StronglyMeasurable (fun p : S × ℝ =>
      normalizedThetaTail (adjointEquiv (F p.1).symm) p.2) := by
    have HE : (fun x => adjointEquiv (F x).symm) =
        fun x => logScaledLattice (adjointEquiv B.symm) (-u x) := by
      funext x
      exact adjointEquiv_logScaledLattice B (u x)
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from congrFun HE]
    exact normalizedThetaTail_joint_stronglyMeasurable
      (B := fun x => logScaledLattice (adjointEquiv B.symm) (-u x))
      (fun z => logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z))
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹| : ℝ) : ℂ) =
      ((|(LinearMap.det B.toLinearMap)⁻¹| : ℝ) : ℂ) := by
    intro x
    dsimp only [F, u]
    rw [logScaledLattice_det, mixedIdealLogScale_sum, Real.exp_zero, one_mul]
  have H := averagedThetaMellinXi_hasSubquadraticGrowth μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (mixedIdealLogScale K I u)) s := by
    funext s
    exact integral_subtype_comap hS
      (fun u => thetaMellinXi (logScaledLattice B (mixedIdealLogScale K I u)) s)
  rw [HE] at H
  exact H


theorem mixedIdealUnitXi_hasSubquadraticGrowth :
    HasSubquadraticGrowth (mixedIdealUnitXi K I) := by
  have H := mixedIdealThetaXi_boundedAverage_hasSubquadraticGrowth K I
    (mixedUnitLogDomain_measurable K) (mixedUnitLogDomain_bounded K)
  apply (H.comp_affine ((Module.finrank ℚ K : ℂ)/2) 0).congr
  intro s
  unfold mixedIdealUnitXi
  congr 1
  funext u
  congr 1
  ring

/-- The genuine entire Dedekind completion has subquadratic growth, for every
number field and without changing the actual discriminant normalization. -/
theorem mixedCompletedDedekindXi_hasSubquadraticGrowth :
    HasSubquadraticGrowth (mixedCompletedDedekindXi K) := by
  have H := HasSubquadraticGrowth.finset_sum Finset.univ
    (fun c : ClassGroup (𝓞 K) => fun s : ℂ =>
      ((FractionalIdeal.absNorm (classRepresentative K c).1 : ℝ) : ℂ)^s *
        mixedIdealUnitXi K (classRepresentative K c) s)
    (fun c _ => (hasSubquadraticGrowth_const_cpow
      (fractionalIdeal_absNorm_pos (classRepresentative K c))).mul
        (mixedIdealUnitXi_hasSubquadraticGrowth K _))
  exact ((hasSubquadraticGrowth_const (mixedXiNormalization K : ℂ)⁻¹).mul
    (hasSubquadraticGrowth_const_cpow (mixedDiscriminantScale_pos K))).mul H

end
end ArtinMatthews.VaryingKummerAnalytic
