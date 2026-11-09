module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.GroupTheory.Coset.Card


set_option backward.privateInPublic true
@[expose] public section

/-! The Galois group of a simple radical extension over a field containing
its roots of unity embeds into the actual roots-of-unity group. No
irreducibility of the defining binomial is assumed. -/

noncomputable section
namespace ArtinMatthews

section General
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
  {q : ℕ} [NeZero q] {ζ : F} (hζ : IsPrimitiveRoot ζ q)

include hζ in
theorem radical_aut_fixes_rootsOfUnity (σ : Gal(L/F)) {z : L} (hz : z ^ q = 1) :
    σ z = z := by
  obtain ⟨j, _, hj⟩ := (hζ.map_of_injective (algebraMap F L).injective).eq_pow_of_pow_eq_one hz
  rw [← hj, map_pow, σ.commutes]

variable {a : F} {α : L} (hα : α ^ q = algebraMap F L a) (hα0 : α ≠ 0)

/-- The actual action on a nonzero radical, as a roots-of-unity character. -/
def radicalAutCharacter : Gal(L/F) →* rootsOfUnity q L where
  toFun σ := rootsOfUnity.mkOfPowEq (σ α / α) (by
    rw [div_pow, ← map_pow, hα, σ.commutes]
    exact div_self (hα ▸ pow_ne_zero q hα0))
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change (1 : Gal(L/F)) α / α = 1
    simp [hα0]
  map_mul' σ τ := by
    apply Subtype.ext
    apply Units.ext
    change σ (τ α) / α = (σ α / α) * (τ α / α)
    have hratio : (τ α / α) ^ q = 1 := by
      rw [div_pow, ← map_pow, hα, τ.commutes]
      exact div_self (hα ▸ pow_ne_zero q hα0)
    have hfix := radical_aut_fixes_rootsOfUnity hζ σ hratio
    have hsplit : τ α = (τ α / α) * α := (div_mul_cancel₀ (τ α) hα0).symm
    conv_lhs => rw [hsplit, map_mul, hfix]
    ring

/-- A radical generating the actual field makes its character injective. -/
theorem radicalAutCharacter_injective
    (hgen : IntermediateField.adjoin F {α} = ⊤) :
    Function.Injective (radicalAutCharacter hζ hα hα0) := by
  intro σ τ heq
  have hratio : σ α / α = τ α / α :=
    congrArg (fun z : rootsOfUnity q L => ((z : Lˣ) : L)) heq
  have hroot : σ α = τ α := (div_left_inj' hα0).mp hratio
  ext x
  have hx : x ∈ IntermediateField.adjoin F {α} := by rw [hgen]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact hroot
  | algebraMap x => rw [σ.commutes, τ.commutes]
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy]
  | inv x hx ihx => rw [map_inv₀, map_inv₀, ihx]
  | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]

include hζ hα hα0 in
/-- The actual automorphism group of any such radical extension is cyclic. -/
theorem radicalExtension_isCyclic
    (hgen : IntermediateField.adjoin F {α} = ⊤) : IsCyclic Gal(L/F) :=
  isCyclic_of_injective (radicalAutCharacter hζ hα hα0)
    (radicalAutCharacter_injective hζ hα hα0 hgen)

include hζ hα hα0 in
/-- In the Galois case its actual field degree divides the radical exponent. -/
theorem radicalExtension_finrank_dvd [FiniteDimensional F L] [IsGalois F L]
    (hgen : IntermediateField.adjoin F {α} = ⊤) : Module.finrank F L ∣ q := by
  have hc := Subgroup.card_dvd_of_injective (radicalAutCharacter hζ hα hα0)
    (radicalAutCharacter_injective hζ hα hα0 hgen)
  rw [IsGalois.card_aut_eq_finrank,
    (hζ.map_of_injective (algebraMap F L).injective).card_rootsOfUnity] at hc
  exact hc

end General
end ArtinMatthews
