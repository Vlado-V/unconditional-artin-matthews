module

public import ArtinMatthews.SLocalSixthUnitImage
public import ArtinMatthews.SLocalHilbertExponent


set_option backward.privateInPublic true
@[expose] public section

/-! Construct the actual sextic isotropic complement by the proved CRT.
The S-unit image transfer and Hilbert exponent identities are both
proved. No maximal-isotropic or source-B hypothesis is supplied. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory
open scoped NumberField Classical
noncomputable section

theorem subgroup_prod_isCompl {G H : Type*} [CommGroup G] [CommGroup H]
    (A C : Subgroup G) (B D : Subgroup H) (hAC : IsCompl A C) (hBD : IsCompl B D) :
    IsCompl (A.prod B) (C.prod D) := by
  rw [isCompl_iff]
  constructor
  · rw [Subgroup.disjoint_def]
    intro x hx hy
    exact Prod.ext (Subgroup.disjoint_def.mp hAC.disjoint hx.1 hy.1)
      (Subgroup.disjoint_def.mp hBD.disjoint hx.2 hy.2)
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    have hA : x.1 ∈ A ⊔ C := by rw [codisjoint_iff.mp hAC.codisjoint]; trivial
    have hB : x.2 ∈ B ⊔ D := by rw [codisjoint_iff.mp hBD.codisjoint]; trivial
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.mp hA
    obtain ⟨b, hb, d, hd, hbd⟩ := Subgroup.mem_sup.mp hB
    exact Subgroup.mem_sup.mpr ⟨(a, b), ⟨ha, hb⟩, (c, d), ⟨hc, hd⟩, Prod.ext hac hbd⟩

variable (K : Type) [Field K] [NumberField K]

def sLocalSixthComplement (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B₂ : Submodule (ZMod 2) (Additive (SLocalPowerClasses K 2 S)))
    (B₃ : Submodule (ZMod 3) (Additive (SLocalPowerClasses K 3 S))) :
    Subgroup (SLocalPowerClasses K 6 S) :=
  ((sLocalComplementSubgroup K 2 S B₂).prod (sLocalComplementSubgroup K 3 S B₃)).comap
    (sLocalSixthCRT K S).toMonoidHom

@[simp] theorem mem_sLocalSixthComplement (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B₂ : Submodule (ZMod 2) (Additive (SLocalPowerClasses K 2 S)))
    (B₃ : Submodule (ZMod 3) (Additive (SLocalPowerClasses K 3 S)))
    (x : SLocalPowerClasses K 6 S) :
    x ∈ sLocalSixthComplement K S B₂ B₃ ↔
      Additive.ofMul (sLocalSixthCRT K S x).1 ∈ B₂ ∧
        Additive.ofMul (sLocalSixthCRT K S x).2 ∈ B₃ := Iff.rfl

theorem sLocalSixthComplement_isCompl (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B₂ : Submodule (ZMod 2) (Additive (SLocalPowerClasses K 2 S)))
    (B₃ : Submodule (ZMod 3) (Additive (SLocalPowerClasses K 3 S)))
    (hB₂ : IsCompl (sUnitPowerSubmodule K 2 S) B₂)
    (hB₃ : IsCompl (sUnitPowerSubmodule K 3 S) B₃) :
    IsCompl (sUnitPowerImage K 6 S) (sLocalSixthComplement K S B₂ B₃) := by
  have hprod := subgroup_prod_isCompl _ _ _ _
    (sLocalComplementSubgroup_isCompl K 2 S B₂ hB₂)
    (sLocalComplementSubgroup_isCompl K 3 S B₃ hB₃)
  have h := (sLocalSixthCRT K S).comapSubgroup.isCompl hprod
  have he : ((sUnitPowerImage K 2 S).prod (sUnitPowerImage K 3 S)).comap
      (sLocalSixthCRT K S).toMonoidHom = sUnitPowerImage K 6 S := by
    ext x
    exact (sLocalSixthCRT_unitImage_iff K S x).symm
  change IsCompl (((sUnitPowerImage K 2 S).prod (sUnitPowerImage K 3 S)).comap
    (sLocalSixthCRT K S).toMonoidHom) (sLocalSixthComplement K S B₂ B₃) at h
  rw [he] at h
  exact h

theorem sLocalSixthComplement_isotropic
    (hmu₂ : (primitiveRoots 2 K).Nonempty) (hmu₃ : (primitiveRoots 3 K).Nonempty)
    (hmu₆ : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B₂ : Submodule (ZMod 2) (Additive (SLocalPowerClasses K 2 S)))
    (B₃ : Submodule (ZMod 3) (Additive (SLocalPowerClasses K 3 S)))
    (hI₂ : ∀ x ∈ B₂, ∀ y ∈ B₂, sLocalHilbertForm K 2 hmu₂ S (Additive.toMul x) (Additive.toMul y) = 1)
    (hI₃ : ∀ x ∈ B₃, ∀ y ∈ B₃, sLocalHilbertForm K 3 hmu₃ S (Additive.toMul x) (Additive.toMul y) = 1) :
    ∀ x ∈ sLocalSixthComplement K S B₂ B₃, ∀ y ∈ sLocalSixthComplement K S B₂ B₃,
      sLocalHilbertForm K 6 hmu₆ S x y = 1 := by
  intro x hx y hy
  obtain ⟨hx₂, hx₃⟩ := (mem_sLocalSixthComplement K S B₂ B₃ x).mp hx
  obtain ⟨hy₂, hy₃⟩ := (mem_sLocalSixthComplement K S B₂ B₃ y).mp hy
  have hi₂ : sLocalHilbertForm K 2 hmu₂ S (sLocalSixthCRT K S x).1 (sLocalSixthCRT K S y).1 = 1 :=
    hI₂ _ hx₂ _ hy₂
  have hi₃ : sLocalHilbertForm K 3 hmu₃ S (sLocalSixthCRT K S x).2 (sLocalSixthCRT K S y).2 = 1 :=
    hI₃ _ hx₃ _ hy₃
  have h₃ : (sLocalHilbertForm K 6 hmu₆ S x y).val ^ 3 = 1 := by
    rw [← sLocalHilbertForm_sixth_square K hmu₂ hmu₆ S x y,
      hi₂]
    rfl
  have h₂ : (sLocalHilbertForm K 6 hmu₆ S x y).val ^ 2 = 1 := by
    rw [← sLocalHilbertForm_sixth_cube K hmu₃ hmu₆ S x y,
      hi₃]
    rfl
  apply Subtype.ext
  have h := pow_succ (sLocalHilbertForm K 6 hmu₆ S x y).val 2
  rw [h₃, h₂, one_mul] at h
  exact h.symm

theorem source_sixth_isotropic_complement {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ B : Subgroup (SLocalPowerClasses K 6 (sourceHilbertSet K S₀)),
      IsCompl (sUnitPowerImage K 6 (sourceHilbertSet K S₀)) B ∧
      ∀ x ∈ B, ∀ y ∈ B,
        sLocalHilbertForm K 6 (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ))
          (sourceHilbertSet K S₀) x y = 1 := by
  obtain ⟨B₂, B₃, hC₂, hC₃, hI₂, hI₃⟩ := source_two_three_isotropic_complements K hζ S₀
  exact ⟨sLocalSixthComplement K _ B₂ B₃, sLocalSixthComplement_isCompl K _ B₂ B₃ hC₂ hC₃,
    sLocalSixthComplement_isotropic K _ _ _ _ B₂ B₃ hI₂ hI₃⟩

end
end ArtinMatthews
