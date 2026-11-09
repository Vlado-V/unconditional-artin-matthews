module

public import ArtinMatthews.SourceHyperbolicProductCalculus
public import OAI.MathematicalPhysics.BFSS.RellichCompactness


set_option backward.privateInPublic true
@[expose] public section

/-! Flatten the actual product coordinates with their Lebesgue measure and coordinate derivatives. -/
namespace ArtinMatthews
open MeasureTheory Set OAI.CubicEisenstein SourceHyperbolicGreen
open scoped Topology ContDiff BigOperators ENNReal Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev HyperbolicFlatSpace (ι : Type*) := EuclideanSpace ℝ (ι × Fin 3)

def sourceHyperbolicFlatten (ι : Type*) [Fintype ι] : ProductSpace ι ≃L[ℝ] HyperbolicFlatSpace ι :=
  ({ toFun := fun p => WithLp.toLp 2 (fun ij : ι × Fin 3 => p ij.1 ij.2)
     invFun := fun x i => WithLp.toLp 2 (fun j : Fin 3 => x (i,j))
     left_inv := by intro p; ext i j; rfl
     right_inv := by intro p; ext ij; rfl
     map_add' := by intro p q; ext ij; rfl
     map_smul' := by intro c p; ext ij; rfl } : ProductSpace ι ≃ₗ[ℝ] HyperbolicFlatSpace ι).toContinuousLinearEquiv

theorem sourceHyperbolicFlatten_apply (p : ProductSpace ι) (i : ι) (j : Fin 3) :
    sourceHyperbolicFlatten ι p (i,j) = p i j := rfl

theorem sourceHyperbolicFlatten_symm_apply (p : HyperbolicFlatSpace ι) (i : ι) (j : Fin 3) :
    (sourceHyperbolicFlatten ι).symm p i j = p (i,j) := rfl

theorem sourceHyperbolicUncurry_measurePreserving :
    MeasurePreserving (Function.uncurry : (ι → Fin 3 → ℝ) → (ι × Fin 3 → ℝ)) := by
  have hm : Measurable (Function.uncurry : (ι → Fin 3 → ℝ) → (ι × Fin 3 → ℝ)) :=
    measurable_pi_iff.mpr (fun ij => (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))
  refine ⟨hm,?_⟩
  change Measure.map Function.uncurry (Measure.pi (fun _ : ι => (volume : Measure (Fin 3 → ℝ)))) =
    Measure.pi (fun _ : ι × Fin 3 => (volume : Measure ℝ))
  symm
  apply Measure.pi_eq
  intro s hs
  have hp : (Function.uncurry : (ι → Fin 3 → ℝ) → (ι × Fin 3 → ℝ)) ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext p
    simp [Set.mem_pi, Function.uncurry, Prod.forall]
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),hp,Measure.pi_pi]
  change (∏ i : ι, (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)))
      (univ.pi (fun j => s (i,j)))) = _
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

theorem sourceHyperbolicFlatten_measurePreserving : MeasurePreserving (sourceHyperbolicFlatten ι) := by
  have hpi : MeasurePreserving (fun p : ProductSpace ι => fun i => WithLp.ofLp (p i)) :=
    measurePreserving_pi (fun _ : ι => (volume : Measure EuclideanSpatial))
      (fun _ : ι => (volume : Measure (Fin 3 → ℝ))) (fun _ => PiLp.volume_preserving_ofLp (Fin 3))
  exact (PiLp.volume_preserving_toLp (ι × Fin 3)).comp
    (sourceHyperbolicUncurry_measurePreserving.comp hpi)

theorem sourceHyperbolicFlatten_symm_single (i : ι) (j : Fin 3) :
    (sourceHyperbolicFlatten ι).symm (EuclideanSpace.single (i,j) (1 : ℝ)) = productDirection i j := by
  ext k l
  by_cases hi : k = i <;> by_cases hj : l = j <;>
    simp [sourceHyperbolicFlatten_symm_apply, productDirection, euclideanCoordinateVector,
      EuclideanSpace.single, Pi.single_apply, Prod.mk.injEq, hi, hj, eq_comm]
  all_goals aesop

theorem sourceHyperbolicFlatten_partial {f : ProductSpace ι → ℂ} (hf : ContDiff ℝ 1 f)
    (p : ProductSpace ι) (i : ι) (j : Fin 3) :
    fderiv ℝ (f ∘ (sourceHyperbolicFlatten ι).symm) (sourceHyperbolicFlatten ι p)
      (EuclideanSpace.single (i,j) (1 : ℝ)) = productPartial f i j p := by
  let e := sourceHyperbolicFlatten ι
  have hS : HasFDerivAt (e.symm : HyperbolicFlatSpace ι → ProductSpace ι)
      e.symm.toContinuousLinearMap (e p) := e.symm.toContinuousLinearMap.hasFDerivAt
  have hF := (hf.differentiable (by norm_num) (e.symm (e p))).hasFDerivAt.comp (e p) hS
  rw [hF.fderiv,ContinuousLinearMap.comp_apply,e.symm_apply_apply]
  change fderiv ℝ f p (e.symm (EuclideanSpace.single (i,j) (1 : ℝ))) = _
  rw [sourceHyperbolicFlatten_symm_single]
  rfl

theorem sourceHyperbolicFlatten_fderiv_norm_sq_le {f : ProductSpace ι → ℂ} (hf : ContDiff ℝ 1 f)
    (p : ProductSpace ι) :
    ‖fderiv ℝ (f ∘ (sourceHyperbolicFlatten ι).symm) (sourceHyperbolicFlatten ι p)‖^2 ≤
      (Fintype.card (ι × Fin 3) : ℝ) * ∑ i, ∑ j : Fin 3, ‖productPartial f i j p‖^2 := by
  classical
  simpa only [Fintype.sum_prod_type,sourceHyperbolicFlatten_partial hf] using
    OAI.BFSSRellich.opNorm_sq_le_coordinate_sum
      (fderiv ℝ (f ∘ (sourceHyperbolicFlatten ι).symm) (sourceHyperbolicFlatten ι p))

end
end ArtinMatthews
