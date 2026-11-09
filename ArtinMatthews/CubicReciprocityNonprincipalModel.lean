module

public import ArtinMatthews.CubicReciprocityNonprincipalAlgebra
public import OAI.NumberTheory.CubicGram.Coordinates
public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete Eisenstein ring comparison needed by cubic numerator characters. -/

namespace ArtinMatthews

open OAI

lemma cubicMoment_omega_eq_hecke_omega :
    CubicFirstMoment.omega = EisensteinEmbedding.omega3 := by
  rw [CubicFirstMoment.omega_eq]
  unfold EisensteinEmbedding.omega3
  push_cast
  ring

lemma hecke_coordinateSubring_eq_cubicMoment :
    ConcreteTraceCRT.coordinateSubring = CubicFirstMoment.eisensteinRing.toSubring := by
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨a, b, hz⟩
    change z ∈ CubicFirstMoment.eisensteinRing
    rw [hz, ← cubicMoment_omega_eq_hecke_omega]
    apply CubicFirstMoment.eisensteinRing.add_mem
    · exact CubicFirstMoment.eisensteinRing.algebraMap_mem a
    · exact CubicFirstMoment.eisensteinRing.mul_mem
        (CubicFirstMoment.eisensteinRing.algebraMap_mem b)
        (Algebra.subset_adjoin (Set.mem_singleton _))
  · intro hz
    obtain ⟨a, b, hab⟩ := CubicFirstMoment.exists_coordinates
      (⟨z, hz⟩ : CubicFirstMoment.Eisenstein)
    exact ⟨a, b, by simpa only [cubicMoment_omega_eq_hecke_omega] using hab⟩

/-- A concrete ring isomorphism preserving the chosen complex embedding. -/
noncomputable def heckeIntegersEquivCubicEisenstein :
    OAI.SevenEighths.HeckeFamily.O ≃+* CubicFirstMoment.Eisenstein :=
  ConcreteTraceCRT.ringOfIntegersEquivCoordinateSubring.trans
    (RingEquiv.subringCongr hecke_coordinateSubring_eq_cubicMoment)

@[simp] theorem heckeIntegersEquivCubicEisenstein_coe
    (x : OAI.SevenEighths.HeckeFamily.O) :
    (heckeIntegersEquivCubicEisenstein x : ℂ) = ConcreteTraceCRT.eisEmbedding x := rfl

/-- Nontriviality of the original Kummer Fourier character gives the exact
noncube hypothesis for the complete cubic numerator-character theorem. -/
theorem cubicFourier_radical_not_cube_in_cubicMoment {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ)) :
    ¬ ∃ y : CubicFirstMoment.Eisenstein, y ^ 3 = (A : CubicFirstMoment.Eisenstein) := by
  rintro ⟨y, hy⟩
  apply cubicFourier_radical_not_cube_in_heckeIntegers χ hχ hR0 hR hrep
  refine ⟨heckeIntegersEquivCubicEisenstein.symm y, ?_⟩
  rw [← map_pow, hy, map_intCast]

end ArtinMatthews
