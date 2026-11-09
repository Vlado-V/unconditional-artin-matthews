module

public import ArtinMatthews.CubicReciprocityBridgeCoordinates
public import ArtinMatthews.CubicReciprocityBridgeCoordinatesAbstract


set_option backward.privateInPublic true
@[expose] public section

/-! Converting the actual additive Fourier characters to unit-valued Kummer characters. -/

namespace ArtinMatthews

open scoped BigOperators

/-- The unit-valued multiplicative character underlying an additive Fourier
character of the tagged actual Galois group. -/
noncomputable def cubicFourierUnitCharacter {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    integerCubicGaloisGroup S →* ℂˣ where
  toFun σ := Units.mk0 (χ (Additive.ofMul σ)) ((χ.val_isUnit _).ne_zero)
  map_one' := by
    apply Units.ext
    exact χ.map_zero_eq_one
  map_mul' σ τ := by
    apply Units.ext
    exact χ.map_add_eq_mul (Additive.ofMul σ) (Additive.ofMul τ)

@[simp] theorem cubicFourierUnitCharacter_coe {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (σ : integerCubicGaloisGroup S) :
    (cubicFourierUnitCharacter χ σ : ℂ) = χ (Additive.ofMul σ) := rfl

/-- Every actual Fourier character is a product of the actual radical
coordinates, with exponents zero, one or two. -/
theorem cubicFourier_character_decomposition {S : Finset ℤ}
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ e : S → Fin 3, ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ∏ i, (cubicCoordinateCharacter r hr hr0 i σ : ℂ) ^ (e i : ℕ) := by
  obtain ⟨e, he⟩ := separating_cubic_characters_generate
    (cubicCoordinateCharacter r hr hr0)
    (cubicCoordinateCharacter_cube r hr hr0)
    (cubicCoordinateCharacters_injective r hr hr0) (cubicFourierUnitCharacter χ)
  refine ⟨e, fun σ => ?_⟩
  have h := congrArg (fun u : ℂˣ => (u : ℂ)) (he σ)
  simpa only [cubicFourierUnitCharacter_coe, Units.coe_prod, Units.val_pow_eq_pow_val] using h

/-- The same character is the ratio `σ(R)/R` for one explicit product radical. -/
theorem cubicFourier_character_as_product_root {S : Finset ℤ}
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ e : S → Fin 3, ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) =
        ((σ.val (cubicProductRoot r (fun i => (e i : ℕ))) /
          cubicProductRoot r (fun i => (e i : ℕ)) : integerCubicField S) : ℂ) := by
  obtain ⟨e, he⟩ := cubicFourier_character_decomposition r hr hr0 χ
  exact ⟨e, fun σ => (he σ).trans
    (cubicCoordinateCharacter_product r hr hr0 (fun i => (e i : ℕ)) σ)⟩

/-- No choice of radicals need be supplied: every Fourier character on the
actual group is attached to an actual nonzero integral cubic radical in its
Kummer field. Its radicand is a product of the selected integer bases. -/
theorem cubicFourier_character_has_radical {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ e : S → Fin 3, ∃ R : integerCubicField S,
      R ≠ 0 ∧ R ^ 3 = (cubicProductRadicand (fun i => (e i : ℕ)) : integerCubicField S) ∧
      ∀ σ : integerCubicGaloisGroup S,
        χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ) := by
  let r := selectedIntegerCubicRoot S
  have hr := selectedIntegerCubicRoot_cube S
  have hr0 := selectedIntegerCubicRoot_ne_zero S hzero
  obtain ⟨e, he⟩ := cubicFourier_character_as_product_root r hr hr0 χ
  refine ⟨e, cubicProductRoot r (fun i => (e i : ℕ)),
    cubicProductRoot_ne_zero r hr0 _, cubicProductRoot_cube r hr _, he⟩

end ArtinMatthews
