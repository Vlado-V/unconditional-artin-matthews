module

public import ArtinMatthews.SLocalHilbertAlternating
public import ArtinMatthews.SLocalPowerModule
public import Mathlib.LinearAlgebra.BilinearForm.Properties


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Hilbert product as a bilinear form over Z/nZ, using an
actual primitive root to identify the values with Z/nZ. Its arithmetic
isotropy, nondegeneracy and exact square-cardinality are retained. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields GlobalClassFieldTheory.Reciprocity
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem sLocalPrimitiveRoots (n : ℕ+) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    (primitiveRoots (n : ℕ) K).Nonempty :=
  ⟨(ζ : K), (mem_primitiveRoots n.pos).mpr (IsPrimitiveRoot.coe_units_iff.mpr hζ)⟩

def sLocalBilinearForm (n : ℕ+) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    LinearMap.BilinForm (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)) := by
  let log := sLocalRootLog K n hζ
  let H := sLocalHilbertForm K n (sLocalPrimitiveRoots K n hζ) S
  let f : Additive (SLocalPowerClasses K n S) →+
      (Additive (SLocalPowerClasses K n S) →ₗ[ZMod (n : ℕ)] ZMod (n : ℕ)) :=
    { toFun := fun x =>
        (log.toAddMonoidHom.comp (H (Additive.toMul x)).toAdditive).toZModLinearMap (n : ℕ)
      map_zero' := by
        ext z
        change log (Additive.ofMul (H 1 (Additive.toMul z))) = 0
        rw [map_one, MonoidHom.one_apply]
        exact map_zero log
      map_add' := by
        intro x y
        ext z
        change log (Additive.ofMul (H (Additive.toMul x * Additive.toMul y) (Additive.toMul z))) =
          log (Additive.ofMul (H (Additive.toMul x) (Additive.toMul z))) +
            log (Additive.ofMul (H (Additive.toMul y) (Additive.toMul z)))
        rw [map_mul, MonoidHom.mul_apply]
        exact log.map_add _ _ }
  exact f.toZModLinearMap (n : ℕ)

@[simp] theorem sLocalBilinearForm_apply (n : ℕ+) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x y : Additive (SLocalPowerClasses K n S)) :
    sLocalBilinearForm K n hζ S x y = sLocalRootLog K n hζ (Additive.ofMul
      (sLocalHilbertForm K n (sLocalPrimitiveRoots K n hζ) S (Additive.toMul x) (Additive.toMul y))) := rfl

theorem sLocalBilinearForm_nondegenerate (n : ℕ+) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sLocalBilinearForm K n hζ S).Nondegenerate := by
  constructor
  · intro x hx
    change Additive.toMul x = 1
    apply sLocalHilbertForm_nondegenerate_left K n (sLocalPrimitiveRoots K n hζ) S
    intro y
    exact (sLocalRootLog_eq_zero_iff K n hζ _).mp (hx (Additive.ofMul y))
  · intro y hy
    change Additive.toMul y = 1
    apply sLocalHilbertForm_nondegenerate_right K n (sLocalPrimitiveRoots K n hζ) S
    intro x
    exact (sLocalRootLog_eq_zero_iff K n hζ _).mp (hy (Additive.ofMul x))

theorem sLocalBilinearForm_isAlt (n : ℕ+) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (hminus : ∃ a : Kˣ, a ^ (n : ℕ) = -1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : (sLocalBilinearForm K n hζ S).IsAlt := by
  intro x
  rw [sLocalBilinearForm_apply, sLocalHilbertForm_diag_eq_one K n _ hminus]
  exact map_zero (sLocalRootLog K n hζ)

def sUnitPowerSubmoduleEquiv (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitPowerSubmodule K n S ≃ sUnitPowerImage K n S where
  toFun x := ⟨Additive.toMul x.val, x.property⟩
  invFun x := ⟨Additive.ofMul x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [NumberField.IsTotallyComplex K]

theorem sLocalBilinearForm_unitSubmodule_isotropic (n : ℕ+) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : powerResidueExponentFinitePlaces K n ⊆ S) :
    ∀ x ∈ sUnitPowerSubmodule K n S, ∀ y ∈ sUnitPowerSubmodule K n S,
      sLocalBilinearForm K n hζ S x y = 0 := by
  intro x hx y hy
  rw [sLocalBilinearForm_apply]
  apply (sLocalRootLog_eq_zero_iff K n hζ _).mpr
  exact sLocalHilbertForm_unitImage_isotropic K n (Nat.cast_ne_zero.mpr n.ne_zero)
    (sLocalPrimitiveRoots K n hζ) S hS _ ((mem_sUnitPowerSubmodule K n S x).mp hx)
    _ ((mem_sUnitPowerSubmodule K n S y).mp hy)

theorem sLocalBilinearForm_card_relation (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    Nat.card (Additive (SLocalPowerClasses K n S)) = (Nat.card (sUnitPowerSubmodule K n S)) ^ 2 := by
  rw [Nat.card_congr (sUnitPowerSubmoduleEquiv K n S)]
  exact sLocalPowerClasses_card_eq_unitImage_sq K n hmu S hS

theorem sLocalBilinearForm_finite (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    Finite (Additive (SLocalPowerClasses K n S)) := by
  apply Nat.finite_of_card_ne_zero
  change Nat.card (SLocalPowerClasses K n S) ≠ 0
  rw [sLocalPowerClasses_card K n hmu S (fun v hv =>
    hS (mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast n ∅ hv))]
  exact pow_ne_zero _ n.ne_zero

end
end ArtinMatthews
