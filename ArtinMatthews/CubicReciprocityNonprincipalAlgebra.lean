module

public import ArtinMatthews.CubicReciprocityBridgeCharacters
public import ArtinMatthews.CubicThetaFieldComparison


set_option backward.privateInPublic true
@[expose] public section

/-!
# Nontrivial Kummer characters have noncube radicands

This is the algebraic input to nonprincipality of the cubic residue Hecke
character. If its radicand had a cube root in the cyclotomic base, every
relative Galois automorphism would fix the chosen radical and the original
Fourier character would be trivial.
-/

namespace ArtinMatthews

open scoped BigOperators

/-- A radical representing a nontrivial Fourier character cannot become a
cube in the actual cubic cyclotomic base field. -/
theorem cubicFourier_radical_not_cube_in_base {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ)) :
    ¬ ∃ y : cubicCyclotomicField, y ^ 3 = (A : cubicCyclotomicField) := by
  rintro ⟨y, hy⟩
  let inc : cubicCyclotomicField →ₐ[ℚ] integerCubicField S :=
    IntermediateField.inclusion (cubicCyclotomicField_le_cubicKummerField (integerCubicBases S))
  let yK := inc y
  have hyK : yK ^ 3 = (A : integerCubicField S) := by
    change inc y ^ 3 = _
    rw [← map_pow, hy, map_intCast]
  have hy0 : yK ≠ 0 := by
    intro h
    have hh : R ^ 3 = 0 := by rw [hR, ← hyK, h, zero_pow (by decide)]
    exact (pow_ne_zero 3 hR0) hh
  let t : integerCubicField S := R / yK
  have ht3 : t ^ 3 = 1 := by
    dsimp [t]
    rw [div_pow, hR, ← hyK, div_self (pow_ne_zero _ hy0)]
  have hty : t * yK = R := div_mul_cancel₀ _ hy0
  have hfix : ∀ σ : integerCubicGaloisGroup S, σ.val R = R := by
    intro σ
    have hσt := cubicKummer_aut_fixes_cube_roots σ.property t ht3
    have hσy : σ.val yK = yK := by
      apply (IntermediateField.mem_fixingSubgroup_iff
        (cubicKummerBase (integerCubicBases S)) σ.val).mp σ.property
      exact y.property
    rw [← hty, map_mul, hσt, hσy]
  apply hχ
  ext h
  change χ h = 1
  have hh := hrep h.toMul
  change χ h = _ at hh
  simpa [hfix, div_self hR0] using hh

/-- Noncube status persists in every ring mapped into the actual base field. -/
theorem cubicFourier_radical_not_cube_of_map {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ))
    {B : Type*} [Ring B] (f : B →+* cubicCyclotomicField) :
    ¬ ∃ y : B, y ^ 3 = (A : B) := by
  rintro ⟨y, hy⟩
  apply cubicFourier_radical_not_cube_in_base χ hχ hR0 hR hrep
  refine ⟨f y, ?_⟩
  rw [← map_pow, hy, map_intCast]

/-- In particular the radicand is not a cube in the actual ring of integers
used by the finite-conductor Hecke-character construction. -/
theorem cubicFourier_radical_not_cube_in_heckeIntegers {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ)) :
    ¬ ∃ y : OAI.SevenEighths.HeckeFamily.O,
      y ^ 3 = (A : OAI.SevenEighths.HeckeFamily.O) := by
  exact cubicFourier_radical_not_cube_of_map χ hχ hR0 hR hrep
    (heckeCyclotomicEquiv.toRingHom.comp (algebraMap OAI.SevenEighths.HeckeFamily.O OAI.SevenEighths.HeckeFamily.K))

end ArtinMatthews
