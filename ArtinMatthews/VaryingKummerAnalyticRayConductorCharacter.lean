module

public import ArtinMatthews.VaryingKummerAnalyticRayConductor
public import ArtinMatthews.VaryingKummerAnalyticRayClassRepresentatives


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive conductor presentation of the actual frozen ray residue data. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical
variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem residue_descent_nonprincipal {M f : Ideal (𝓞 K)} (hMf : M ≤ f)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk f a) else 0)
    (hχ : χ ≠ 1) : φ ≠ 1 := by
  intro heq
  apply hχ
  apply MulChar.ext'
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  by_cases ha : IsUnit (Ideal.Quotient.mk M a)
  · have hf : IsUnit (Ideal.Quotient.mk f a) := by
      simpa only [Ideal.Quotient.factor_mk] using ha.map (Ideal.Quotient.factor hMf)
    rw [hmask a, ite_eq_left ha, heq, MulChar.one_apply hf, MulChar.one_apply ha]
  · rw [hmask a, ite_eq_right ha, MulChar.map_nonunit _ ha]

namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

/-- Actual ray data produce a primitive finite residue character at a
genuinely constructed conductor, including the original-unit mask. -/
theorem exists_primitive_residue_conductor :
    ∃ (f : Ideal (𝓞 K)) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
      (hMf : rationalModulusIdeal (𝓞 K) N ≤ f),
      f ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
        if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
          then φ (Ideal.Quotient.mk f a) else 0) ∧
      φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMf).toMonoidHom) = ψ.residue.toUnitHom ∧
      ∀ u : (𝓞 K)ˣ, φ (Ideal.Quotient.mk f (u : 𝓞 K)) = 1 :=
  exists_primitive_residue_conductor_trivial_on_units
    (rationalModulusIdeal (𝓞 K) N) (rationalModulusIdeal_ne_bot N) ψ.residue ψ.residue_unit

/-- Nontriviality of the actual original residue character is retained by
the descended primitive character, rather than postulated. -/
theorem exists_primitive_residue_conductor_nontrivial (hres : ψ.residue ≠ 1) :
    ∃ (f : Ideal (𝓞 K)) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
      (hMf : rationalModulusIdeal (𝓞 K) N ≤ f),
      f ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
        if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
          then φ (Ideal.Quotient.mk f a) else 0) ∧
      φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMf).toMonoidHom) = ψ.residue.toUnitHom ∧
      (∀ u : (𝓞 K)ˣ, φ (Ideal.Quotient.mk f (u : 𝓞 K)) = 1) ∧ φ ≠ 1 := by
  obtain ⟨f, φ, hMf, hf, hprimitive, hnorm, hmask, hfactor, hunit⟩ :=
    ψ.exists_primitive_residue_conductor
  exact ⟨f, φ, hMf, hf, hprimitive, hnorm, hmask, hfactor, hunit,
    residue_descent_nonprincipal hMf ψ.residue φ hmask hres⟩

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
