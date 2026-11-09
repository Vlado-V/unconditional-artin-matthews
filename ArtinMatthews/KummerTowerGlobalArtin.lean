module

public import ArtinMatthews.ArtinAbelianGlobalEuler
public import ArtinMatthews.KummerCyclotomicTower


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine global Artin Euler factorizations for the actual auxiliary
cyclotomic/Kummer tower, on Re(s)>1. -/
noncomputable section
namespace ArtinMatthews
open scoped NumberField IsMulCommutative BigOperators

variable (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]

local instance cyclotomicGlobalArtinCharactersFintype :
    Fintype (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) := Fintype.ofFinite _
local instance kummerGlobalArtinCharactersFintype :
    Fintype (Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ) := Fintype.ofFinite _

/-- Global factorization over the actual cyclotomic field ℚ(ζ_(12q)). -/
theorem twelfthKummer_cyclotomic_globalArtinFactorization {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (twelfthKummerField q a) s =
      ∏ χ : Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ,
        AbelianLocal.abelianArtinEulerProduct (twelfthCyclotomicField q)
          (twelfthKummerField q a) χ s :=
  AbelianLocal.dedekindZeta_eq_prod_abelianArtinEulerProduct _ _ hs

/-- Global factorization over the actual original Kummer field. -/
theorem twelfthKummer_original_globalArtinFactorization {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (twelfthKummerField q a) s =
      ∏ χ : Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ,
        AbelianLocal.abelianArtinEulerProduct (primeKummerField q a)
          (twelfthKummerField q a) χ s :=
  AbelianLocal.dedekindZeta_eq_prod_abelianArtinEulerProduct _ _ hs

end ArtinMatthews
