module

public import ArtinMatthews.CubicGaloisFourier
public import Mathlib.GroupTheory.FiniteAbelian.Duality


set_option backward.privateInPublic true
@[expose] public section

/-!
# Actual Kummer coordinate characters

Choosing one nonzero cube root for each base gives characters
`σ ↦ σ(r_a)/r_a`. They take values in the complex cube roots of unity
and jointly separate the actual relative Galois group.
-/

namespace ArtinMatthews

open scoped BigOperators

variable {S : Finset ℤ}

/-- A Kummer coordinate, before passage to the fixed complex embedding. -/
noncomputable def cubicCoordinateValue
    (r : S → integerCubicField S) (i : S) (σ : integerCubicGaloisGroup S) :
    integerCubicField S := σ.val (r i) / r i

lemma cubicCoordinateValue_cube
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) (i : S) (σ : integerCubicGaloisGroup S) :
    cubicCoordinateValue r i σ ^ 3 = 1 := by
  unfold cubicCoordinateValue
  rw [div_pow, ← map_pow, hr i, map_intCast, ← hr i, div_self]
  exact pow_ne_zero _ (hr0 i)

lemma cubicCoordinateValue_ne_zero
    (r : S → integerCubicField S) (hr0 : ∀ i, r i ≠ 0)
    (i : S) (σ : integerCubicGaloisGroup S) : cubicCoordinateValue r i σ ≠ 0 := by
  apply div_ne_zero _ (hr0 i)
  intro hz
  apply hr0 i
  apply σ.val.injective
  simpa only [map_zero] using hz

lemma cubicCoordinateValue_mul
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) (i : S) (σ τ : integerCubicGaloisGroup S) :
    cubicCoordinateValue r i (σ * τ) = cubicCoordinateValue r i σ * cubicCoordinateValue r i τ := by
  have hfix := cubicKummer_aut_fixes_cube_roots σ.property
    (cubicCoordinateValue r i τ) (cubicCoordinateValue_cube r hr hr0 i τ)
  have hσr : σ.val (r i) ≠ 0 := by
    intro hz
    apply hr0 i
    apply σ.val.injective
    simpa only [map_zero] using hz
  have heq : σ.val (τ.val (r i)) = cubicCoordinateValue r i τ * σ.val (r i) := by
    apply (div_eq_iff hσr).mp
    simpa only [cubicCoordinateValue, map_div₀] using hfix
  change σ.val (τ.val (r i)) / r i = _
  rw [heq]
  unfold cubicCoordinateValue
  ring

/-- The actual complex-valued unit character attached to a chosen radical. -/
noncomputable def cubicCoordinateCharacter
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) (i : S) : integerCubicGaloisGroup S →* ℂˣ where
  toFun σ := Units.mk0 ((cubicCoordinateValue r i σ : integerCubicField S) : ℂ)
    (by exact_mod_cast cubicCoordinateValue_ne_zero r hr0 i σ)
  map_one' := by
    apply Units.ext
    change ((r i / r i : integerCubicField S) : ℂ) = 1
    rw [div_self (hr0 i)]
    rfl
  map_mul' σ τ := by
    apply Units.ext
    change ((cubicCoordinateValue r i (σ * τ) : integerCubicField S) : ℂ) =
      ((cubicCoordinateValue r i σ : integerCubicField S) : ℂ) *
        ((cubicCoordinateValue r i τ : integerCubicField S) : ℂ)
    exact_mod_cast cubicCoordinateValue_mul r hr hr0 i σ τ

@[simp] theorem cubicCoordinateCharacter_coe
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) (i : S) (σ : integerCubicGaloisGroup S) :
    (cubicCoordinateCharacter r hr hr0 i σ : ℂ) =
      ((σ.val (r i) / r i : integerCubicField S) : ℂ) := rfl

@[simp] theorem cubicCoordinateCharacter_cube
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) (i : S) (σ : integerCubicGaloisGroup S) :
    cubicCoordinateCharacter r hr hr0 i σ ^ 3 = 1 := by
  apply Units.ext
  change ((cubicCoordinateValue r i σ : integerCubicField S) : ℂ) ^ 3 = 1
  exact_mod_cast cubicCoordinateValue_cube r hr hr0 i σ

/-- All radical coordinates together determine the actual Galois automorphism. -/
theorem cubicCoordinateCharacters_injective
    (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) :
    Function.Injective (fun σ : integerCubicGaloisGroup S =>
      fun i : S => cubicCoordinateCharacter r hr hr0 i σ) := by
  intro σ τ hστ
  have hroot : ∀ i, σ.val (r i) = τ.val (r i) := by
    intro i
    have hv := congrArg (fun u : ℂˣ => (u : ℂ)) (congrFun hστ i)
    change ((σ.val (r i) / r i : integerCubicField S) : ℂ) =
      ((τ.val (r i) / r i : integerCubicField S) : ℂ) at hv
    have hdiv : σ.val (r i) / r i = τ.val (r i) / r i := by exact_mod_cast hv
    have hm := congrArg (fun z : integerCubicField S => z * r i) hdiv
    simpa only [div_mul_cancel₀ _ (hr0 i)] using hm
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext ℚ
  intro z hz
  let x : integerCubicField S := ⟨z, IntermediateField.subset_adjoin ℚ _ hz⟩
  change σ.val x = τ.val x
  rcases (mem_cubicKummerPolynomial_rootSet_iff (integerCubicBases S) z).mp hz with
    hz3 | ⟨a, ha, hz3⟩
  · have hx3 : x ^ 3 = 1 := by apply Subtype.ext; exact hz3
    rw [cubicKummer_aut_fixes_cube_roots σ.property x hx3,
      cubicKummer_aut_fixes_cube_roots τ.property x hx3]
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    let i : S := ⟨b, hb⟩
    have hx3 : x ^ 3 = r i ^ 3 := by
      rw [hr i]
      apply Subtype.ext
      change z ^ 3 = (b : ℂ)
      simpa only [Rat.cast_intCast] using hz3
    let t : integerCubicField S := x / r i
    have ht3 : t ^ 3 = 1 := by
      dsimp [t]
      rw [div_pow, hx3, div_self (pow_ne_zero _ (hr0 i))]
    have htσ := cubicKummer_aut_fixes_cube_roots σ.property t ht3
    have htτ := cubicKummer_aut_fixes_cube_roots τ.property t ht3
    have htx : t * r i = x := div_mul_cancel₀ _ (hr0 i)
    rw [← htx, map_mul, map_mul, htσ, htτ, hroot i]

/-- A product of chosen radicals with arbitrary natural exponents. -/
noncomputable def cubicProductRoot (r : S → integerCubicField S) (e : S → ℕ) :
    integerCubicField S := ∏ i, r i ^ e i

/-- The corresponding integer radicand. -/
def cubicProductRadicand (e : S → ℕ) : ℤ := ∏ i, i.val ^ e i

theorem cubicProductRoot_ne_zero (r : S → integerCubicField S)
    (hr0 : ∀ i, r i ≠ 0) (e : S → ℕ) : cubicProductRoot r e ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hr0 i))

/-- The product radical has the literal integer product as its cube. -/
theorem cubicProductRoot_cube (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S)) (e : S → ℕ) :
    cubicProductRoot r e ^ 3 = (cubicProductRadicand e : integerCubicField S) := by
  unfold cubicProductRoot cubicProductRadicand
  rw [← Finset.prod_pow]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, Nat.mul_comm, pow_mul, hr i]

/-- Products of coordinate characters are the character attached to the
single product radical. This is the form used in cubic reciprocity. -/
theorem cubicCoordinateCharacter_product (r : S → integerCubicField S)
    (hr : ∀ i, r i ^ 3 = (i.val : integerCubicField S))
    (hr0 : ∀ i, r i ≠ 0) (e : S → ℕ) (σ : integerCubicGaloisGroup S) :
    (∏ i, ((cubicCoordinateCharacter r hr hr0 i σ : ℂ) ^ e i)) =
      ((σ.val (cubicProductRoot r e) / cubicProductRoot r e : integerCubicField S) : ℂ) := by
  unfold cubicProductRoot
  rw [map_prod, ← Finset.prod_div_distrib]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubicCoordinateCharacter_coe, map_pow]
  push_cast
  rw [div_pow]

/-- A fixed actual cube root for each selected integer base. -/
noncomputable def selectedIntegerCubicRoot (S : Finset ℤ) (i : S) : integerCubicField S :=
  Classical.choose (exists_integerCubicField_root i.property)

theorem selectedIntegerCubicRoot_cube (S : Finset ℤ) (i : S) :
    selectedIntegerCubicRoot S i ^ 3 = (i.val : integerCubicField S) :=
  Classical.choose_spec (exists_integerCubicField_root i.property)

theorem selectedIntegerCubicRoot_ne_zero (S : Finset ℤ)
    (hzero : ∀ a ∈ S, a ≠ 0) (i : S) : selectedIntegerCubicRoot S i ≠ 0 := by
  intro hz
  have h := selectedIntegerCubicRoot_cube S i
  rw [hz, zero_pow (by decide)] at h
  exact hzero i.val i.property (by exact_mod_cast h.symm)

end ArtinMatthews
