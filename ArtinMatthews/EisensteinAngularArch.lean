module

public import ArtinMatthews.EisensteinAngularEmbedding
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.Data.Fintype.EquivFin


set_option backward.privateInPublic true
@[expose] public section

/-! Exactly one oriented relative embedding is chosen over each complex
place. The norm-pullback angular character therefore has exponent +1
or -1 at every complex place and has no radial factor. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ConcreteTraceCRT NumberField
open scoped NumberField BigOperators Classical
noncomputable section

local instance : IsCyclotomicExtension {3} ℚ BaseField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : Algebra BaseField ℂ := baseComplexEmbedding.toAlgebra
variable (F : Type*) [Field F] [NumberField F] [Algebra BaseField F]

def relativePlaceMap (σ : F →ₐ[BaseField] ℂ) : InfinitePlace F :=
  InfinitePlace.mk σ.toRingHom

omit [NumberField F] in
theorem relativePlaceMap_injective : Function.Injective (relativePlaceMap F) := by
  intro σ τ h
  rcases InfinitePlace.mk_eq_iff.mp h with he | he
  · exact AlgHom.toRingHom_injective he
  · exfalso
    apply baseComplexEmbedding_not_conjugate
    ext x
    change star (baseComplexEmbedding x) = baseComplexEmbedding x
    have hx := congrArg (fun f : F →+* ℂ => f (algebraMap BaseField F x)) he
    change star (σ (algebraMap BaseField F x)) = τ (algebraMap BaseField F x) at hx
    simpa only [AlgHom.commutes,
      RingHom.algebraMap_toAlgebra] using hx

theorem extension_nrRealPlaces_zero : InfinitePlace.nrRealPlaces F = 0 := by
  have hζ : IsPrimitiveRoot
      (algebraMap BaseField F (IsCyclotomicExtension.zeta 3 ℚ BaseField)) 3 :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ BaseField).map_of_injective
      (algebraMap BaseField F).injective
  exact InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide) hζ

theorem relativePlaceMap_card :
    Fintype.card (F →ₐ[BaseField] ℂ) = Fintype.card (InfinitePlace F) := by
  have hbase : Module.finrank ℚ BaseField = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank 3 BaseField]
    decide
  have ht := Module.finrank_mul_finrank ℚ BaseField F
  rw [hbase] at ht
  have hp := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [extension_nrRealPlaces_zero F,zero_add] at hp
  have he := AlgHom.card BaseField F ℂ
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    extension_nrRealPlaces_zero F,zero_add]
  omega

def relativePlaceEquiv : (F →ₐ[BaseField] ℂ) ≃ InfinitePlace F :=
  Equiv.ofBijective (relativePlaceMap F)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨relativePlaceMap_injective F,relativePlaceMap_card F⟩)

def chosenRelativeEmbedding (w : InfinitePlace F) : F →ₐ[BaseField] ℂ :=
  (relativePlaceEquiv F).symm w

theorem chosenRelativeEmbedding_mk (w : InfinitePlace F) :
    InfinitePlace.mk (chosenRelativeEmbedding F w).toRingHom = w :=
  (relativePlaceEquiv F).apply_symm_apply w

theorem chosenRelativeEmbedding_eq_or_conjugate (w : InfinitePlace F) :
    (chosenRelativeEmbedding F w).toRingHom = w.embedding ∨
      (chosenRelativeEmbedding F w).toRingHom = ComplexEmbedding.conjugate w.embedding := by
  have h := InfinitePlace.embedding_mk_eq (chosenRelativeEmbedding F w).toRingHom
  rw [chosenRelativeEmbedding_mk] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    simpa only [ComplexEmbedding.conjugate,star_star] using
      (congrArg ComplexEmbedding.conjugate h).symm

def angularInfinityExponent (w : InfinitePlace F) : ℤ :=
  if (chosenRelativeEmbedding F w).toRingHom = w.embedding then 1 else -1

theorem angularInfinityExponent_eq_one_or_neg_one (w : InfinitePlace F) :
    angularInfinityExponent F w = 1 ∨ angularInfinityExponent F w = -1 := by
  unfold angularInfinityExponent
  split_ifs <;> simp

theorem complexAngular_conjugate (z : ℂ) : complexAngular (star z) = (complexAngular z)⁻¹ := by
  by_cases hz : z=0
  · simp [hz,complexAngular]
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  simp only [complexAngular,norm_star,inv_div]
  apply (div_eq_div_iff hn hz).mpr
  simpa only [pow_two,Complex.star_def] using Complex.conj_mul' z

theorem chosenRelativeEmbedding_angular (w : InfinitePlace F) (a : F) :
    complexAngular (chosenRelativeEmbedding F w a) =
      complexAngular (w.embedding a) ^ angularInfinityExponent F w := by
  by_cases h : (chosenRelativeEmbedding F w).toRingHom = w.embedding
  · rw [angularInfinityExponent,ite_eq_left h,zpow_one]
    exact congrArg complexAngular (congrArg (fun f : F →+* ℂ => f a) h)
  · have hc := (chosenRelativeEmbedding_eq_or_conjugate F w).resolve_left h
    rw [angularInfinityExponent,ite_eq_right h,zpow_neg_one]
    change complexAngular ((chosenRelativeEmbedding F w).toRingHom a) = _
    rw [hc,ComplexEmbedding.conjugate_coe_eq]
    exact complexAngular_conjugate _

theorem angularArchimedean_place_product (a : F) :
    angularArchimedean F a =
      ∏ w : InfinitePlace F, complexAngular (w.embedding a) ^ angularInfinityExponent F w := by
  calc
    _ = ∏ w : InfinitePlace F, complexAngular (chosenRelativeEmbedding F w a) :=
      ((relativePlaceEquiv F).symm.prod_comp
        (fun σ : F →ₐ[BaseField] ℂ => complexAngular (σ a))).symm
    _ = _ := Finset.prod_congr rfl (fun w _ => chosenRelativeEmbedding_angular F w a)

theorem angularNormIdeal_principal_infinityType (a : 𝓞 F) (ha : a ≠ 0)
    (hthree : (3 : 𝓞 F) ∣ a-1) :
    angularNormIdeal F (Ideal.span {a}) =
      ∏ w : InfinitePlace F, complexAngular (w.embedding (a : F)) ^ angularInfinityExponent F w := by
  rw [angularNormIdeal_principal_archimedean F a ha hthree,angularArchimedean_place_product]

end
end ArtinMatthews.AngularLambda
