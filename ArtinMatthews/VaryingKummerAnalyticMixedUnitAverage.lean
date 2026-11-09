module

public import ArtinMatthews.VaryingKummerAnalyticMixedTheta
public import ArtinMatthews.VaryingKummerAnalyticMixedLogCoordinates
public import ArtinMatthews.VaryingKummerAnalyticThetaDualAverages


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Dirichlet-unit average of the mixed-signature ideal theta
continuation is entire. The uniform-integrability argument adapts the generic
proof in OpenAI PrimePackets/LatticeDuality.lean, lines 258–320, to the actual
mixed-signature unit coordinates. No real-embedding ordering is assumed.
The final identification with the Dedekind Dirichlet series is separate. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Compact subsets of the actual unit-log space have bounded Gaussian log scales. -/
theorem mixedIdealLogScale_abs_bound {S : Set (logSpace K)} (hS : IsCompact S) :
    ∃ R : ℝ, ∀ u ∈ S, ∀ i, |mixedIdealLogScale K I u i| ≤ R := by
  let f : logSpace K → ℝ := fun u => ∑ i, |mixedIdealLogScale K I u i|
  have hf : Continuous f := continuous_finsetSum _ (fun i _ =>
    (mixedIdealLogScale_continuous K I i).abs)
  obtain ⟨R, hR⟩ := hS.bddAbove_image hf.continuousOn
  refine ⟨R, fun u hu i => le_trans ?_ (hR (Set.mem_image_of_mem f hu))⟩
  exact Finset.single_le_sum (fun j _ => abs_nonneg (mixedIdealLogScale K I u j))
    (Finset.mem_univ i)

/-- The unit-log Gaussian flow written as a literal sum over ideal elements. -/
def mixedIdealFlowTheta (u : logSpace K) (t : ℝ) : ℂ :=
  ∑' a : I.1, Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
    ‖logScale (mixedIdealLogScale K I u)
      ((mixedIdealOrthonormalBasis K I).repr (mixedIdealEmbedding K I a))‖^2)

/-- The family being averaged is precisely the Gaussian flow of the actual ideal. -/
theorem mixedIdealFlowTheta_eq_normalizedTheta (u : logSpace K) (t : ℝ) :
    mixedIdealFlowTheta K I u t =
      normalizedTheta (logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)) t := by
  symm
  unfold mixedIdealFlowTheta normalizedTheta latticeTheta
  have he (z : MixedIdealIndex K I → ℤ) :
      mixedIdealMatrix K I (euclideanInteger z) =
        (mixedIdealOrthonormalBasis K I).repr
          (mixedIdealEmbedding K I ((fractionalIdealBasis K I.1).equivFun.symm z)) := by
    change (mixedIdealOrthonormalBasis K I).repr
      ((mixedIdealEuclideanBasis K I).equivFun.symm (fun j => (z j : ℝ))) = _
    rw [mixedIdealEuclideanBasis_integer_apply]
  change (∑' z : MixedIdealIndex K I → ℤ,
    Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ‖logScale (mixedIdealLogScale K I u) (mixedIdealMatrix K I (euclideanInteger z))‖^2)) = _
  simp_rw [he]
  exact (fractionalIdealBasis K I.1).equivFun.symm.toEquiv.tsum_eq
    (fun a : I.1 => Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ‖logScale (mixedIdealLogScale K I u)
        ((mixedIdealOrthonormalBasis K I).repr (mixedIdealEmbedding K I a))‖^2))

/-- Averaging the actual mixed-signature ideal theta over any bounded measurable
part of the unit-log space preserves its entire continuation. -/
theorem mixedIdealThetaXi_boundedAverage_entire {S : Set (logSpace K)}
    (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (fun s => ∫ u in S,
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
  have H := averagedThetaMellinXi_differentiable μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (mixedIdealLogScale K I u)) s := by
    funext s
    exact integral_subtype_comap hS
      (fun u => thetaMellinXi (logScaledLattice B (mixedIdealLogScale K I u)) s)
  rw [HE] at H
  exact H

/-- Unit-averaged continuation, in the standard Dedekind spectral variable.
This is a construction; no identification with a completed L-function is asserted here. -/
def mixedIdealUnitXi (s : ℂ) : ℂ :=
  ∫ u in mixedUnitLogDomain K,
    thetaMellinXi (logScaledLattice (mixedIdealMatrix K I)
      (mixedIdealLogScale K I u)) ((Module.finrank ℚ K : ℂ) * s / 2)

/-- The actual unit-domain average is entire for every number field. -/
theorem mixedIdealUnitXi_entire : Differentiable ℂ (mixedIdealUnitXi K I) := by
  exact (mixedIdealThetaXi_boundedAverage_entire K I
    (mixedUnitLogDomain_measurable K) (mixedUnitLogDomain_bounded K)).comp (by fun_prop)

end
end ArtinMatthews.VaryingKummerAnalytic
