module

public import ArtinMatthews.KummerRadicalCyclic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact power-class kernel of the actual radical character in a common
finite Galois field. No irreducibility or character-injectivity assumption is
made: the fixed-field theorem identifies the kernel. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]
variable {n : ℕ} [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n)
variable {a b : F} {α β : L}
variable (hα : α^n = algebraMap F L a) (hα0 : α ≠ 0)
variable (hβ : β^n = algebraMap F L b) (hβ0 : β ≠ 0)

theorem radicalAutCharacter_eq_iff_ratio_in_base :
    radicalAutCharacter hζ hα hα0 = radicalAutCharacter hζ hβ hβ0 ↔
      ∃ t : F, algebraMap F L t = α/β := by
  constructor
  · intro h
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := L) (α/β)).mpr
    intro σ
    have H := congrArg (fun χ : Gal(L/F) →* rootsOfUnity n L =>
      ((χ σ : Lˣ) : L)) h
    change σ α / α = σ β / β at H
    rw [map_div₀]
    have hσβ : σ β ≠ 0 := by simpa only [map_zero] using σ.injective.ne hβ0
    apply (div_eq_div_iff hσβ hβ0).2
    simpa only [mul_comm] using (div_eq_div_iff hα0 hβ0).1 H
  · rintro ⟨t,ht⟩
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.ext
    change σ α / α = σ β / β
    have H : σ (α/β) = α/β := by rw [← ht,σ.commutes]
    rw [map_div₀] at H
    have hσβ : σ β ≠ 0 := by simpa only [map_zero] using σ.injective.ne hβ0
    apply (div_eq_div_iff hα0 hβ0).2
    simpa only [mul_comm] using (div_eq_div_iff hσβ hβ0).1 H

theorem radicalAutCharacter_eq_iff_exists_pow :
    radicalAutCharacter hζ hα hα0 = radicalAutCharacter hζ hβ hβ0 ↔
      ∃ t : F, t^n = a/b := by
  rw [radicalAutCharacter_eq_iff_ratio_in_base hζ hα hα0 hβ hβ0]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t, (algebraMap F L).injective ?_⟩
    rw [map_pow,ht,div_pow,hα,hβ,map_div₀]
  · rintro ⟨t,ht⟩
    have hp : (α/β)^n = (algebraMap F L t)^n := by
      rw [div_pow,hα,hβ,← map_div₀,← ht,map_pow]
    have ht0 : algebraMap F L t ≠ 0 := by
      intro hz
      rw [hz,zero_pow (NeZero.ne n)] at hp
      exact pow_ne_zero _ (div_ne_zero hα0 hβ0) hp
    have hr : ((α/β)/(algebraMap F L t))^n = 1 := by
      rw [div_pow,hp,div_self (pow_ne_zero _ ht0)]
    obtain ⟨j,_hj,hj⟩ := (hζ.map_of_injective (algebraMap F L).injective).eq_pow_of_pow_eq_one hr
    refine ⟨ζ^j*t,?_⟩
    rw [map_mul,map_pow,hj]
    exact div_mul_cancel₀ (α/β) ht0

theorem radicalAutCharacter_one_iff_exists_pow :
    radicalAutCharacter hζ hα hα0 = 1 ↔ ∃ t : F, t^n = a := by
  have h1 : (1:L)^n = algebraMap F L (1:F) := by simp
  have hc : radicalAutCharacter hζ h1 (one_ne_zero : (1:L) ≠ 0) = 1 := by
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.ext
    simp [radicalAutCharacter]
  simpa only [hc,div_one] using
    radicalAutCharacter_eq_iff_exists_pow hζ hα hα0 h1 (one_ne_zero : (1:L) ≠ 0)

end
end ArtinMatthews
