module

public import ArtinMatthews.QuadraticCharacterFamily
public import ArtinMatthews.ArtinRayFaithfulEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine two-character Dedekind factorization, with the primitive
ray character at its exact conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField AbelianLocal
open scoped NumberField Classical BigOperators
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] [IsTotallyComplex K]

theorem quadraticNormConductor_dedekind_factor
    (hd : Module.finrank K L = 2) (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ)
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      NumberField.dedekindZeta K s * (abelianNormConductorRayCharacter K L χ).dirichlet s := by
  let : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _
  have hc : Nat.card (Gal(L/K)) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hd
  have hne : (1 : Gal(L/K) →* ℂˣ) ≠ χ := (faithfulCharacter_ne_one_of_card_two hc χ hχ).symm
  have hset : (Finset.univ : Finset (Gal(L/K) →* ℂˣ)) = {1, χ} := by
    ext φ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact character_eq_one_or_of_card_two hc χ hχ φ
  rw [dedekindZeta_eq_prod_abelianArtinEulerProduct K L hs, hset, Finset.prod_pair hne,
    abelianArtinEulerProduct_one K L hs, ← abelianNormConductorRayCharacter_dirichlet_eq_artin χ hχ hs]

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
