module

public import ArtinMatthews.EisensteinAngularNorm
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Extend the actual oriented Eisenstein embedding to its fraction
field, and express the norm-pullback angular factor by the genuine
relative complex embeddings. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

def baseComplexEmbedding : BaseField →+* ℂ :=
  IsFractionRing.lift eisEmbedding_injective

theorem baseComplexEmbedding_integer (a : BaseIntegers) :
    baseComplexEmbedding (a : BaseField) = eisEmbedding a :=
  IsFractionRing.lift_algebraMap eisEmbedding_injective a

theorem baseComplexEmbedding_gen :
    baseComplexEmbedding (EisensteinEmbedding.pb.gen : BaseField) = EisensteinEmbedding.omega3 := by
  rw [baseComplexEmbedding_integer]
  exact EisensteinEmbedding.embedding_gen _ _

theorem baseComplexEmbedding_not_conjugate :
    NumberField.ComplexEmbedding.conjugate baseComplexEmbedding ≠ baseComplexEmbedding := by
  intro he
  have h := congrArg (fun f : BaseField →+* ℂ => f (EisensteinEmbedding.pb.gen : BaseField)) he
  change star (baseComplexEmbedding (EisensteinEmbedding.pb.gen : BaseField)) =
    baseComplexEmbedding (EisensteinEmbedding.pb.gen : BaseField) at h
  rw [baseComplexEmbedding_gen] at h
  have hi := congrArg Complex.im h
  change -EisensteinEmbedding.omega3.im = EisensteinEmbedding.omega3.im at hi
  exact EisensteinEmbedding.omega3_im_ne_zero (by linarith)

local instance : Algebra BaseField ℂ := baseComplexEmbedding.toAlgebra
variable (F : Type*) [Field F] [NumberField F] [Algebra BaseField F]

def angularArchimedean (a : F) : ℂ :=
  ∏ σ : F →ₐ[BaseField] ℂ, complexAngular (σ a)

theorem angularArchimedean_eq_norm (a : F) :
    angularArchimedean F a = complexAngular (baseComplexEmbedding (Algebra.norm BaseField a)) := by
  change (∏ σ : F →ₐ[BaseField] ℂ, complexAngularHom (σ a)) = _
  rw [← map_prod]
  change complexAngular (∏ σ : F →ₐ[BaseField] ℂ, σ a) = _
  apply congrArg complexAngular
  exact (Algebra.norm_eq_prod_embeddings BaseField ℂ a).symm

theorem angularNormIdeal_principal_archimedean (a : 𝓞 F) (ha : a ≠ 0)
    (hthree : (3 : 𝓞 F) ∣ a-1) :
    angularNormIdeal F (Ideal.span {a}) = angularArchimedean F (a : F) := by
  rw [angularNormIdeal_principal F a ha hthree,angularArchimedean_eq_norm]
  congr 1
  rw [← baseComplexEmbedding_integer]
  congr 1
  exact Algebra.algebraMap_intNorm (K := BaseField) (L := F) a

theorem angularArchimedean_norm {a : F} (ha : a ≠ 0) : ‖angularArchimedean F a‖ = 1 := by
  rw [angularArchimedean_eq_norm]
  apply complexAngular_norm
  simpa only [map_zero] using
    baseComplexEmbedding.injective.ne (Algebra.norm_ne_zero_iff.mpr ha)

end
end ArtinMatthews.AngularLambda
