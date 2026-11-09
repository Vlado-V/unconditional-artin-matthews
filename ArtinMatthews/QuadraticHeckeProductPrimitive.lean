module

public import ArtinMatthews.ReflectionProductCharacter
public import ArtinMatthews.SIntegerCharacterTransport
public import Mathlib.Algebra.Group.Pi.Units


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped Classical BigOperators
noncomputable section

theorem primitiveOnIdeals_pullCharacter
    {R T : Type} [CommRing R] [CommRing T] (e : R ≃+* T)
    (χ : MulChar T ℂ) (hχ : IsPrimitiveOnIdeals χ) :
    IsPrimitiveOnIdeals (ArtinMatthews.SIntegerQuotient.pullCharacter e χ) := by
  intro I hI
  have hJ : I.map e.toRingHom ≠ ⊥ := by
    obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    intro h
    have he : e x ∈ I.map e.toRingHom := Ideal.mem_map_of_mem _ hx
    rw [h] at he
    exact (e.map_ne_zero_iff.mpr hne) (Ideal.mem_bot.mp he)
  obtain ⟨u, hu, hne⟩ := hχ _ hJ
  let v := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  · have hm : e.symm ((u : T) - 1) ∈ (I.map e.toRingHom).map e.symm.toRingHom :=
      Ideal.mem_map_of_mem _ hu
    rw [Ideal.map_map] at hm
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; exact e.symm_apply_apply x
    rw [he, Ideal.map_id, map_sub, map_one] at hm
    exact hm
  · change χ (e (e.symm (u : T))) ≠ 1
    rwa [e.apply_symm_apply]

/-- A product of nontrivial residue-field characters is primitive on the
actual product ring. An empty product also satisfies the definition. -/
theorem reflectionProductCharacter_primitiveOnIdeals
    {ι : Type} [Fintype ι] (R : ι → Type) [∀ i, Field (R i)]
    (χ : ∀ i, MulChar (R i) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    IsPrimitiveOnIdeals (reflectionProductCharacter R χ) := by
  intro I hI
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp (hχ i)
  let v : (∀ j, R j)ˣ := MulEquiv.piUnits.symm (Function.update (fun j : ι => (1 : (R j)ˣ)) i u)
  have hv (j : ι) : v.val j = (Function.update (fun j : ι => (1 : (R j)ˣ)) i u j).val := rfl
  refine ⟨v, ?_, ?_⟩
  · have hmem : Pi.single i (((u : R i) - 1) / x i) * x ∈ I := I.mul_mem_left _ hx
    have he : v.val - 1 = Pi.single i (((u : R i) - 1) / x i) * x := by
      funext j
      change v.val j - 1 = Pi.single i (((u : R i) - 1) / x i) j * x j
      rw [hv]
      by_cases hj : j = i
      · subst j
        rw [Function.update_self, Pi.single_eq_same, div_mul_cancel₀ _ hi]
      · rw [Function.update_of_ne hj, Pi.single_eq_of_ne' (Ne.symm hj), zero_mul]
        simp
    rwa [he]
  · change (∏ j, χ j (v.val j)) ≠ 1
    rw [Finset.prod_eq_single i]
    · simpa only [hv, Function.update_self] using hu
    · intro j _ hj
      simp [hv, Function.update_of_ne hj]
    · simp

end
end ArtinMatthews.VaryingKummerAnalytic
