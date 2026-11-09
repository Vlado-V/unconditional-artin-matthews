module

public import ArtinMatthews.PowerClassSixthCRT


set_option backward.privateInPublic true
@[expose] public section

/-! The literal diagonal S-unit image is carried by sixth-power CRT to
the product of its square and cube images. The reverse inclusion uses
an actual S-unit u^3*v^4, not a representative hypothesis. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem mem_sUnitPowerImage_iff_unitClass (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalPowerClasses K n S) :
    x ∈ sUnitPowerImage K n S ↔ ∃ u : SUnitGroup (K := K) S, sLocalUnitClassMap K n S u = x := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨u, hq⟩
  · rintro ⟨u, rfl⟩
    exact ⟨QuotientGroup.mk' _ u, rfl⟩

theorem sLocalSixthCRT_unitImage_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : SLocalPowerClasses K 6 S) :
    x ∈ sUnitPowerImage K 6 S ↔
      (sLocalSixthCRT K S x).1 ∈ sUnitPowerImage K 2 S ∧
        (sLocalSixthCRT K S x).2 ∈ sUnitPowerImage K 3 S := by
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := (mem_sUnitPowerImage_iff_unitClass K 6 S x).mp hx
    rw [sLocalSixthCRT_unitClass]
    exact ⟨(mem_sUnitPowerImage_iff_unitClass K 2 S _).mpr ⟨u, rfl⟩,
      (mem_sUnitPowerImage_iff_unitClass K 3 S _).mpr ⟨u, rfl⟩⟩
  · rintro ⟨hx₂, hx₃⟩
    obtain ⟨u, hu⟩ := (mem_sUnitPowerImage_iff_unitClass K 2 S _).mp hx₂
    obtain ⟨v, hv⟩ := (mem_sUnitPowerImage_iff_unitClass K 3 S _).mp hx₃
    let w : SUnitGroup (K := K) S := u ^ 3 * v ^ 4
    have hu₂ : (sLocalUnitClassMap K 2 S u) ^ 2 = 1 := sLocalPowerClasses_pow_eq_one K 2 S _
    have hv₂ : (sLocalUnitClassMap K 2 S v) ^ 2 = 1 := sLocalPowerClasses_pow_eq_one K 2 S _
    have hu₃ : (sLocalUnitClassMap K 3 S u) ^ 3 = 1 := sLocalPowerClasses_pow_eq_one K 3 S _
    have hv₃ : (sLocalUnitClassMap K 3 S v) ^ 3 = 1 := sLocalPowerClasses_pow_eq_one K 3 S _
    have hu₂' : (sLocalUnitClassMap K 2 S u) ^ 3 = sLocalUnitClassMap K 2 S u := by
      rw [show 3 = 2 + 1 by decide, pow_succ, hu₂, one_mul]
    have hv₂' : (sLocalUnitClassMap K 2 S v) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by decide, pow_mul, hv₂, one_pow]
    have hv₃' : (sLocalUnitClassMap K 3 S v) ^ 4 = sLocalUnitClassMap K 3 S v := by
      rw [show 4 = 3 + 1 by decide, pow_succ, hv₃, one_mul]
    have hw₂ : sLocalUnitClassMap K 2 S w = (sLocalSixthCRT K S x).1 := by
      change sLocalUnitClassMap K 2 S (u ^ 3 * v ^ 4) = _
      rw [map_mul, map_pow, map_pow, hu₂', hv₂', mul_one, hu]
    have hw₃ : sLocalUnitClassMap K 3 S w = (sLocalSixthCRT K S x).2 := by
      change sLocalUnitClassMap K 3 S (u ^ 3 * v ^ 4) = _
      rw [map_mul, map_pow, map_pow, hu₃, hv₃', one_mul, hv]
    apply (mem_sUnitPowerImage_iff_unitClass K 6 S x).mpr
    refine ⟨w, (sLocalSixthCRT K S).injective ?_⟩
    rw [sLocalSixthCRT_unitClass]
    exact Prod.ext hw₂ hw₃

def sLocalSubgroupEquivSubmodule (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SLocalPowerClasses K n S) ≃o
      Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n : ℕ))

def sLocalComplementSubgroup (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B : Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S))) :
    Subgroup (SLocalPowerClasses K n S) := (sLocalSubgroupEquivSubmodule K n S).symm B

@[simp] theorem mem_sLocalComplementSubgroup (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B : Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)))
    (x : SLocalPowerClasses K n S) :
    x ∈ sLocalComplementSubgroup K n S B ↔ Additive.ofMul x ∈ B := Iff.rfl

theorem sLocalComplementSubgroup_isCompl (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B : Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)))
    (hB : IsCompl (sUnitPowerSubmodule K n S) B) :
    IsCompl (sUnitPowerImage K n S) (sLocalComplementSubgroup K n S B) :=
  (sLocalSubgroupEquivSubmodule K n S).symm.isCompl hB

end
end ArtinMatthews
