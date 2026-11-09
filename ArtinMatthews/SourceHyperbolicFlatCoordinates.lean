module

public import ArtinMatthews.SourceHyperbolicProductCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


set_option backward.privateInPublic true
@[expose] public section

/-! The Cartesian coordinates of the product upper half spaces, with their exact flat volume. -/

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory
open scoped BigOperators Classical
noncomputable section

variable (ι : Type*) [Fintype ι]

def productFlatEuclideanEquiv : ProductSpace ι ≃L[ℝ] EuclideanSpace ℝ (ι × Fin 3) :=
  ({
    toFun := fun x => WithLp.toLp 2 (fun ij => x ij.1 ij.2)
    invFun := fun z i => WithLp.toLp 2 (fun j => z (i,j))
    left_inv := fun _ => rfl
    right_inv := by intro z; ext ij; cases ij; rfl
    map_add' := by intro x y; ext ij; rfl
    map_smul' := by intro a x; ext ij; rfl
  } : ProductSpace ι ≃ₗ[ℝ] EuclideanSpace ℝ (ι × Fin 3)).toContinuousLinearEquiv

@[simp]
theorem productFlatEuclideanEquiv_apply (x : ProductSpace ι) (i : ι) (j : Fin 3) :
    productFlatEuclideanEquiv ι x (i,j) = x i j := rfl

@[simp]
theorem productFlatEuclideanEquiv_symm_apply (z : EuclideanSpace ℝ (ι × Fin 3))
    (i : ι) (j : Fin 3) : (productFlatEuclideanEquiv ι).symm z i j = z (i,j) := rfl

theorem productFlatEuclideanEquiv_measurePreserving :
    MeasurePreserving (productFlatEuclideanEquiv ι) volume volume := by
  let raw : ProductSpace ι → (ι × Fin 3 → ℝ) := fun x ij => x ij.1 ij.2
  have hm : Measurable raw := Measurable.of_eval fun ij =>
    (measurable_pi_apply ij.2).comp
      ((PiLp.volume_preserving_ofLp (Fin 3)).measurable.comp (measurable_pi_apply ij.1))
  have hraw : MeasurePreserving raw volume volume := by
    refine ⟨hm, ?_⟩
    symm
    rw [volume_pi]
    apply Measure.pi_eq
    intro s hs
    let rect (i : ι) : Set (Fin 3 → ℝ) := Set.univ.pi fun j => s (i,j)
    have hrect (i : ι) : MeasurableSet (rect i) :=
      MeasurableSet.univ_pi fun j => hs (i,j)
    have he : raw ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i => WithLp.ofLp ⁻¹' rect i) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi, raw, rect]
      exact ⟨fun h i j => h (i,j), fun h ij => h ij.1 ij.2⟩
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), he, volume_pi_pi,
      Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin 3)).measurable (hrect i),
      (PiLp.volume_preserving_ofLp (Fin 3)).map_eq]
    change volume (Set.univ.pi fun j : Fin 3 => s (i,j)) = _
    rw [volume_pi_pi]
  exact (PiLp.volume_preserving_toLp (ι × Fin 3)).comp hraw

theorem productFlatEuclideanEquiv_direction (i : ι) (j : Fin 3) :
    productFlatEuclideanEquiv ι (productDirection i j) =
      EuclideanSpace.basisFun (ι × Fin 3) ℝ (i,j) := by
  rw [EuclideanSpace.basisFun_apply]
  ext ⟨k,l⟩
  by_cases h : k = i
  · subst k
    simp [productDirection, euclideanCoordinateVector, PiLp.single_apply, Pi.single_apply]
  · simp [productDirection, Pi.single_eq_of_ne h, PiLp.single_apply, h]

theorem productFlatEuclideanEquiv_partial (f : ProductSpace ι → ℂ)
    (x : ProductSpace ι) (hf : DifferentiableAt ℝ f x) (i : ι) (j : Fin 3) :
    fderiv ℝ (f ∘ (productFlatEuclideanEquiv ι).symm) (productFlatEuclideanEquiv ι x)
        (EuclideanSpace.basisFun (ι × Fin 3) ℝ (i,j)) =
      productPartial f i j x := by
  let e := productFlatEuclideanEquiv ι
  have hf' : DifferentiableAt ℝ f (e.symm (e x)) := by simpa using hf
  have he := (e.symm : EuclideanSpace ℝ (ι × Fin 3) →L[ℝ] ProductSpace ι).hasFDerivAt
    (x := e x)
  change fderiv ℝ (f ∘ e.symm) (e x) _ = _
  rw [(hf'.hasFDerivAt.comp (e x) he).fderiv, e.symm_apply_apply]
  change fderiv ℝ f x (e.symm _) = fderiv ℝ f x (productDirection i j)
  rw [← productFlatEuclideanEquiv_direction ι i j]
  exact congrArg (fderiv ℝ f x) (e.symm_apply_apply _)

end
end ArtinMatthews.SourceHyperbolicGreen
