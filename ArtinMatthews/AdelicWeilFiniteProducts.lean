module

public import ArtinMatthews.StandardAdelicWeilProduct
public import ArtinMatthews.FiniteOrderProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite forms of the actual adelic Weil product. Finite support
is a consequence of the proved product and the local eighth-root theorem. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ)

include d in
theorem adelicNormalizedWeil_hasFiniteMulSupport (x : Fˣ) :
    Function.HasFiniteMulSupport (adelicNormalizedWeil F ψ x) :=
  hasFiniteMulSupport_of_eighth _ (adelicNormalizedWeil_hasProd F ψ d x)
    (adelicNormalizedWeil_eighth F ψ d x)

include d in
theorem adelicNormalizedWeil_finprod (x : Fˣ) : ∏ᶠ v, adelicNormalizedWeil F ψ x v = 1 := by
  have h : ∏' v, adelicNormalizedWeil F ψ x v = 1 :=
    (adelicNormalizedWeil_hasProd F ψ d x).tprod_eq
  rwa [tprod_eq_finprod (adelicNormalizedWeil_hasFiniteMulSupport F ψ d x)] at h

include d in
theorem adelicNormalizedWeil_prod_eq_one (x : Fˣ)
    (S : Finset (ArchimedeanAdeles.Construction.Places F))
    (hS : ∀ v ∉ S, adelicNormalizedWeil F ψ x v = 1) :
    ∏ v ∈ S, adelicNormalizedWeil F ψ x v = 1 :=
  (hasProd_prod_of_ne_finset_one hS).unique (adelicNormalizedWeil_hasProd F ψ d x)

include d in
theorem adelicNormalizedWeil_punctured (x : Fˣ)
    (S : Finset (ArchimedeanAdeles.Construction.Places F))
    (v : ArchimedeanAdeles.Construction.Places F) (hv : v ∉ S)
    (hS : ∀ w ∉ insert v S, adelicNormalizedWeil F ψ x w = 1) :
    adelicNormalizedWeil F ψ x v = (∏ w ∈ S, adelicNormalizedWeil F ψ x w)⁻¹ := by
  have h := adelicNormalizedWeil_prod_eq_one F ψ d x (insert v S) hS
  rw [Finset.prod_insert hv] at h
  exact eq_inv_of_mul_eq_one_left h

theorem standardNormalizedWeil_hasFiniteMulSupport (x : Fˣ) :
    Function.HasFiniteMulSupport (standardNormalizedWeil F x) :=
  adelicNormalizedWeil_hasFiniteMulSupport F (StandardAdelic.character F)
    (StandardAdelic.character_data F) x

theorem standardNormalizedWeil_finprod (x : Fˣ) : ∏ᶠ v, standardNormalizedWeil F x v = 1 :=
  adelicNormalizedWeil_finprod F (StandardAdelic.character F) (StandardAdelic.character_data F) x

theorem standardNormalizedWeil_punctured (x : Fˣ)
    (S : Finset (ArchimedeanAdeles.Construction.Places F))
    (v : ArchimedeanAdeles.Construction.Places F) (hv : v ∉ S)
    (hS : ∀ w ∉ insert v S, standardNormalizedWeil F x w = 1) :
    standardNormalizedWeil F x v = (∏ w ∈ S, standardNormalizedWeil F x w)⁻¹ :=
  adelicNormalizedWeil_punctured F (StandardAdelic.character F) (StandardAdelic.character_data F) x S v hv hS

end

end ArtinMatthews.QuadraticWeil
