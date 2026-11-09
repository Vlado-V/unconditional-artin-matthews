module

public import ArtinMatthews.SLocalUnitImage
public import Mathlib.Algebra.Module.ZMod


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical Z/nZ module on the actual local power quotient and
the actual S-unit image submodule. Primitive roots give an actual
additive logarithm of the roots of unity. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem powerQuotient_pow_eq_one {G : Type*} [CommGroup G]
    (n : ℕ) (q : G ⧸ (powMonoidHom n : G →* G).range) : q ^ n = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩

theorem sLocalPowerClasses_pow_eq_one (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalPowerClasses K n S) :
    x ^ (n : ℕ) = 1 := by
  funext v
  exact powerQuotient_pow_eq_one (n : ℕ) (x v)

instance sLocalPowerClasses_zmodModule (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)) :=
  AddCommGroup.zmodModule (fun x => sLocalPowerClasses_pow_eq_one K n S (Additive.toMul x))

def sUnitPowerSubmodule (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)) :=
  AddSubgroup.toZModSubmodule (n : ℕ) (Subgroup.toAddSubgroup (sUnitPowerImage K n S))

@[simp] theorem mem_sUnitPowerSubmodule (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Additive (SLocalPowerClasses K n S)) :
    x ∈ sUnitPowerSubmodule K n S ↔
      Additive.toMul x ∈ (sUnitPowerImage K n S : Set (SLocalPowerClasses K n S)) := Iff.rfl

def sLocalRootLog (n : ℕ+) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    Additive (rootsOfUnity (n : ℕ) K) ≃+ ZMod (n : ℕ) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact ((MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive.symm).trans hζ.zmodEquivZPowers.symm

omit [NumberField K] in
theorem sLocalRootLog_eq_zero_iff (n : ℕ+) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) (z : rootsOfUnity (n : ℕ) K) :
    sLocalRootLog K n hζ (Additive.ofMul z) = 0 ↔ z = 1 := by
  constructor
  · intro hz
    have h : Additive.ofMul z = (0 : Additive (rootsOfUnity (n : ℕ) K)) := by
      apply (sLocalRootLog K n hζ).injective
      simpa only [map_zero] using hz
    exact h
  · intro hz
    subst z
    exact map_zero (sLocalRootLog K n hζ)

end
end ArtinMatthews
