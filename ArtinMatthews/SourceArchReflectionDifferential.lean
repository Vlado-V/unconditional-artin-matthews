module

public import ArtinMatthews.SourceArchMobiusDifferential


set_option backward.privateInPublic true
@[expose] public section

/-! The signed Weyl transformation and its exact horizontal differential
at a vertical point. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein Filter
open scoped Topology InnerProductSpace
noncomputable section

def sourceArchReflection (B : ℂ) (p : EuclideanSpatial) : EuclideanSpatial :=
  euclideanComplexDilation B (euclideanWeylAction p)

def sourceArchReflectionDerivative (B : ℂ) (p : EuclideanSpatial) :
    EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  (euclideanComplexDilation B).comp (sourceArchWeylDerivative p)

theorem sourceArchReflection_hasFDerivAt (B : ℂ) (p : EuclideanSpatial) (hp : 0 < p 2) :
    HasFDerivAt (sourceArchReflection B) (sourceArchReflectionDerivative B p) p :=
  (euclideanComplexDilation B).hasFDerivAt.comp p
    (sourceArchWeyl_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp))

private theorem norm_vertical (p : EuclideanSpatial) (h0 : p 0 = 0) (h1 : p 1 = 0)
    (hp : 0 < p 2) : ‖p‖ = p 2 := by
  have h : ‖p‖ ^ 2 = (p 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,h0,h1]
    simp
  nlinarith [norm_nonneg p]

theorem sourceArchReflection_vertical (B : ℂ) (p : EuclideanSpatial)
    (h0 : p 0 = 0) (h1 : p 1 = 0) (hp : 0 < p 2) :
    sourceArchReflection B p = WithLp.toLp 2 ![0, 0, Complex.normSq B / p 2] := by
  obtain ⟨hx,hy,hz⟩ := euclideanWeylAction_apply p
  obtain ⟨g0,g1,g2⟩ := euclideanComplexDilation_apply B (euclideanWeylAction p)
  rw [h0,mul_zero,neg_zero] at hx
  rw [h1,mul_zero] at hy
  rw [hx,hy] at g0 g1
  rw [hz,norm_vertical p h0 h1 hp] at g2
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext j
  fin_cases j
  · change sourceArchReflection B p 0 = 0
    simpa only [sourceArchReflection,mul_zero,sub_zero] using g0
  · change sourceArchReflection B p 1 = 0
    simpa only [sourceArchReflection,mul_zero,add_zero] using g1
  · change sourceArchReflection B p 2 = Complex.normSq B / p 2
    rw [sourceArchReflection,g2]
    field_simp [hp.ne']

private theorem inversion_horizontal (p : EuclideanSpatial) (j : Fin 3)
    (hj : p j = 0) :
    euclideanInversionDeriv p (euclideanCoordinateVector j) =
      (1 / ‖p‖) ^ 2 • euclideanCoordinateVector j := by
  have hmem : euclideanCoordinateVector j ∈ (ℝ ∙ p)ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change inner ℝ p (EuclideanSpace.single j (1 : ℝ)) = 0
    simp [EuclideanSpace.inner_single_right,hj]
  change (1 / ‖p‖) ^ 2 • (ℝ ∙ p)ᗮ.reflection (euclideanCoordinateVector j) = _
  rw [Submodule.reflection_mem_subspace_eq_self hmem]

theorem sourceArchReflectionDerivative_horizontal (B : ℂ) (p : EuclideanSpatial)
    (h0 : p 0 = 0) (h1 : p 1 = 0) (hp : 0 < p 2) :
    sourceArchReflectionDerivative B p (euclideanCoordinateVector 0) =
      ((p 2)⁻¹)^2 • (-((B ^ 2).re) • euclideanCoordinateVector 0 -
        (B ^ 2).im • euclideanCoordinateVector 1) ∧
    sourceArchReflectionDerivative B p (euclideanCoordinateVector 1) =
      ((p 2)⁻¹)^2 • (-((B ^ 2).im) • euclideanCoordinateVector 0 +
        (B ^ 2).re • euclideanCoordinateVector 1) := by
  have hn := norm_vertical p h0 h1 hp
  have hh (j : Fin 3) (hj : p j = 0) :
      sourceArchReflectionDerivative B p (euclideanCoordinateVector j) =
        ((p 2)⁻¹)^2 • euclideanComplexDilation B (euclideanWeylReflection (euclideanCoordinateVector j)) := by
    rw [sourceArchReflectionDerivative,ContinuousLinearMap.comp_apply,sourceArchWeylDerivative,
      ContinuousLinearMap.comp_apply,inversion_horizontal p j hj,hn,map_smul,map_smul]
    simp [inv_pow,one_div]
  rw [hh 0 h0,hh 1 h1]
  constructor <;> apply congrArg (fun x : EuclideanSpatial => ((p 2)⁻¹)^2 • x)
  all_goals
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext j
    simp only [WithLp.equiv_apply]
    fin_cases j <;>
      simp [euclideanComplexDilation,euclideanWeylReflection,euclideanMatrixOperator_apply,
        Fin.sum_univ_three,euclideanCoordinateVector,Pi.single_apply]

end
end ArtinMatthews.SourceArchJacquet
