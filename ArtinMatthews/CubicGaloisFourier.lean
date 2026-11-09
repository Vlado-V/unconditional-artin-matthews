module

public import ArtinMatthews.CubicFrobeniusConditionKummer
public import ArtinMatthews.FiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-!
# Character expansion on the actual cubic Galois group

The group is proved abelian using the actual complex-conjugation action.
The finite Fourier expansion is then specialized to the constructed
Frobenius condition, with its positive constant coefficient.
-/

namespace ArtinMatthews

open scoped BigOperators NumberField

open Classical

theorem subgroup_mul_comm_of_conjugation_inverts {G : Type*} [Group G]
    (H : Subgroup G) (c : G)
    (hinv : ∀ x ∈ H, c * x * c⁻¹ = x⁻¹) (x y : H) : x * y = y * x := by
  apply Subtype.ext
  apply inv_injective
  change ((x : G) * (y : G))⁻¹ = ((y : G) * (x : G))⁻¹
  calc
    _ = c * ((x : G) * (y : G)) * c⁻¹ :=
      (hinv _ (H.mul_mem x.property y.property)).symm
    _ = (c * (x : G) * c⁻¹) * (c * (y : G) * c⁻¹) := by group
    _ = (x : G)⁻¹ * (y : G)⁻¹ := by rw [hinv _ x.property, hinv _ y.property]
    _ = _ := (mul_inv_rev (y : G) (x : G)).symm

noncomputable instance integerCubicGaloisGroup_commGroup (S : Finset ℤ) :
    CommGroup (integerCubicGaloisGroup S) := by
  let g : Group (integerCubicGaloisGroup S) := inferInstance
  exact { g with
    mul_comm := subgroup_mul_comm_of_conjugation_inverts _
      (cubicKummerConjugation (integerCubicBases S))
      (fun _ h => cubicKummer_conjugation_inverts h) }

noncomputable instance integerCubicGaloisGroup_fintype (S : Finset ℤ) :
    Fintype (integerCubicGaloisGroup S) := Fintype.ofFinite _

theorem integerCubicGaloisGroup_cube (S : Finset ℤ) (h : integerCubicGaloisGroup S) :
    h ^ 3 = 1 := by
  apply Subtype.ext
  exact cubicKummer_aut_cube_eq_one h.property

theorem additiveCubicGaloisGroup_three (S : Finset ℤ)
    (h : Additive (integerCubicGaloisGroup S)) : (3 : ℕ) • h = 0 := by
  change h.toMul ^ 3 = 1
  exact integerCubicGaloisGroup_cube S h.toMul

noncomputable def cubicConditionFinset (S : Finset ℤ) :
    Finset (Additive (integerCubicGaloisGroup S)) :=
  {h : Additive (integerCubicGaloisGroup S) | h.toMul ∈ cubicNonfixingSet S}.toFinset

theorem mem_cubicConditionFinset (S : Finset ℤ) (h : Additive (integerCubicGaloisGroup S)) :
    h ∈ cubicConditionFinset S ↔ h.toMul ∈ cubicNonfixingSet S := by
  simp [cubicConditionFinset]

theorem cubicConditionFinset_inversionStable (S : Finset ℤ) :
    InversionStable (cubicConditionFinset S) := by
  intro h
  simp only [mem_cubicConditionFinset, toMul_neg]
  constructor
  · exact cubicNonfixingSet_inv
  · intro hi
    simpa only [inv_inv] using cubicNonfixingSet_inv hi

noncomputable def cubicConditionDensity (S : Finset ℤ) : ℝ :=
  (cubicConditionFinset S).card / (Fintype.card (integerCubicGaloisGroup S) : ℝ)

theorem cubicConditionDensity_pos {S : Finset ℤ} (hB : ¬ ObstructionB S)
    (hrel : ∃ T : Finset ℤ, T ⊆ S ∧ Even T.card ∧
      NegativeThreeRationalSquare (∏ a ∈ T, a)) :
    0 < cubicConditionDensity S := by
  obtain ⟨h, hh⟩ := cubicNonfixingSet_nonempty hB hrel
  have hne : (cubicConditionFinset S).Nonempty :=
    ⟨Additive.ofMul h, (mem_cubicConditionFinset S _).mpr hh⟩
  unfold cubicConditionDensity
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hne)
    (by exact_mod_cast Fintype.card_pos)

/-- Equation (9.2) evaluated at genuine arithmetic Frobenius. Both the finite
group and the simultaneous noncube condition here are the constructed ones. -/
theorem cubicFrobenius_indicator_trace_expansion {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
    (D : IntegralFrobeniusData (integerCubicField S) p) (hp3 : p % 3 = 1)
    (ha0 : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    (if ∀ a ∈ S, ¬ IsCubeMod p a then (1 : ℂ) else 0) =
      ((cubicConditionFinset S).card : ℂ) /
          Fintype.card (Additive (integerCubicGaloisGroup S)) +
        ∑ χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S)),
          ((indicatorFourierCoeff (cubicConditionFinset S) χ).re : ℂ) *
            cubicTrace (χ (Additive.ofMul (relativeCubicFrobenius D hp3))) := by
  classical
  have h := indicator_cubicTrace_expansion_realCoeffs (additiveCubicGaloisGroup_three S)
    (cubicConditionFinset S) (cubicConditionFinset_inversionStable S)
    (Additive.ofMul (relativeCubicFrobenius D hp3))
  simpa only [mem_cubicConditionFinset, toMul_ofMul,
    relativeCubicFrobenius_mem_iff D hp3 ha0] using h

end ArtinMatthews
