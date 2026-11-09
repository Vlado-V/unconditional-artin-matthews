module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Any surjective linear residue coordinate on an ideal differs from the
constructed rank-one trivialization by a unit of the actual quotient ring. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

omit [IsDedekindDomain R] in
theorem idealModuleLinearMap_zero_on_relation (f : I →ₗ[R] R ⧸ M)
    (a : I) (ha : (a:R) ∈ M*I) : f a = 0 := by
  have H : ∀ (b : R) (hb : b ∈ M*I),
      f ⟨b,(Ideal.mul_le_right : M*I ≤ I) hb⟩ = 0 := by
    intro b hb
    refine Submodule.mul_induction_on' (M := M) (N := I)
      (C := fun b hb => f ⟨b,(Ideal.mul_le_right : M*I ≤ I) hb⟩ = 0) ?_ ?_ hb
    · intro r hr x hx
      change f (r • (⟨x,hx⟩ : I)) = 0
      rw [map_smul]
      change Ideal.Quotient.mk M r * f ⟨x,hx⟩ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
    · intro x hx y hy Hx Hy
      change f ((⟨x,(Ideal.mul_le_right : M*I ≤ I) hx⟩ : I) +
        ⟨y,(Ideal.mul_le_right : M*I ≤ I) hy⟩) = 0
      rw [map_add, Hx, Hy, zero_add]
  exact H a ha

theorem idealModuleLinearMap_eq_scalar_coordinate (f : I →ₗ[R] R ⧸ M) (a : I) :
    f a = f ⟨idealModuleGenerator I M hI hM, idealModuleGenerator_mem I M hI hM⟩ *
      idealResidueCoordinate I M hI hM a := by
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (idealResidueCoordinate I M hI hM a)
  have ha := (idealResidueCoordinate_eq_mk_iff I M hI hM a r).mp hr.symm
  let g : I := ⟨idealModuleGenerator I M hI hM, idealModuleGenerator_mem I M hI hM⟩
  have H := idealModuleLinearMap_zero_on_relation I M f (a-r•g) ha
  rw [map_sub, map_smul, sub_eq_zero] at H
  rw [H, ← hr]
  change Ideal.Quotient.mk M r * f g = f g * Ideal.Quotient.mk M r
  ring

theorem idealModuleLinearMap_generator_isUnit (f : I →ₗ[R] R ⧸ M)
    (hf : Function.Surjective f) :
    IsUnit (f ⟨idealModuleGenerator I M hI hM, idealModuleGenerator_mem I M hI hM⟩) := by
  obtain ⟨a,ha⟩ := hf 1
  have H := idealModuleLinearMap_eq_scalar_coordinate I M hI hM f a
  rw [ha] at H
  exact isUnit_iff_exists_inv.mpr ⟨idealResidueCoordinate I M hI hM a,H.symm⟩

/-- Exact scalar comparison with a genuine unit, including quotient rings
with zero divisors and the modulus-one quotient. -/
theorem idealModuleLinearMap_exists_unit (f : I →ₗ[R] R ⧸ M)
    (hf : Function.Surjective f) :
    ∃ u : (R ⧸ M)ˣ, ∀ a : I,
      f a = (u : R ⧸ M) * idealResidueCoordinate I M hI hM a := by
  let hu := idealModuleLinearMap_generator_isUnit I M hI hM f hf
  refine ⟨hu.unit,fun a => ?_⟩
  rw [hu.unit_spec]
  exact idealModuleLinearMap_eq_scalar_coordinate I M hI hM f a

end
end ArtinMatthews.VaryingKummerAnalytic
