module

public import ArtinMatthews.SixthKummerLocalDegree
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces


set_option backward.privateInPublic true
@[expose] public section

/-! The individual sixth-radical higher-unit statement in the exact chosen
local norm subgroup used by the class-field-theory modulus API. -/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations LocalFieldTheory

namespace ArtinMatthews

section General

variable {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- Every actual sixth power lies in the chosen local norm subgroup when
the global Galois degree divides six. The chosen local degree is derived. -/
theorem galois_sixthPowers_le_chosenLocalNorm
    (hdeg : Module.finrank K L ∣ 6) (v : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom (α := (v.adicCompletion K)ˣ) 6).range ≤
      chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v := by
  let a := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra a w.1 w.2
  let E := LocalizedCompletion a w
  let : Module.Finite a.Completion E :=
    localizedCompletionModuleFinite a (RayClass.adicAbv_isNontrivial v) w
  let e := finitePlaceCompletionUnitsContinuousMulEquiv v
  have hd : Module.finrank a.Completion E ∣ 6 := by
    rw [(localizedCompletionEquivCompletion a
      (RayClass.adicAbv_isNontrivial v) w).toLinearEquiv.finrank_eq]
    exact (galois_absoluteCompletion_finrank_dvd a
      (RayClass.adicAbv_isNontrivial v) w).trans hdeg
  intro u hu
  obtain ⟨r, hr⟩ := hu
  change r^6 = u at hr
  let r₀ : a.Completionˣ := e.symm r
  obtain ⟨z, hz⟩ := HenselPower.exists_unit_norm_of_pow
    (R := a.Completion) (K := a.Completion) (L := E) 6 hd (r₀^6) r₀ rfl
  have hznorm : normUnits a.Completion E z = r₀^6 := by
    apply Units.ext
    have h := congrArg Units.val hz
    change Algebra.norm a.Completion (z : E) = ((r₀^6 : a.Completionˣ) : a.Completion) at h
    exact h
  change u ∈ (localNormSubgroup a.Completion E).map e.toMonoidHom
  refine ⟨r₀^6, ⟨z, hznorm⟩, ?_⟩
  change e ((e.symm r)^6) = u
  rw [map_pow, e.apply_symm_apply]
  exact hr

end General

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (a : F) (ha : a ≠ 0)

include hζ ha

theorem sixthKummerIndividual_higherUnit_le_chosenLocalNorm
    (v : HeightOneSpectrum (𝓞 F)) :
    RayClass.localHigherUnitGroup v (sixthLocalHenselDepth v) ≤
      chosenFinitePlaceLocalNormSubgroup (K := F) (L := sixthKummerRowField {a}) v :=
  (sixthLocal_higherUnit_le_sixthPowers v).trans
    (galois_sixthPowers_le_chosenLocalNorm
      (sixthKummerIndividualField_finrank_dvd_six hζ a ha) v)

theorem sixthKummerIndividual_principalUnit_le_chosenLocalNorm
    (v : HeightOneSpectrum (𝓞 F)) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) :
    RayClass.localHigherUnitGroup v 1 ≤
      chosenFinitePlaceLocalNormSubgroup (K := F) (L := sixthKummerRowField {a}) v := by
  simpa only [sixthLocalHenselDepth_eq_one v h6] using
    sixthKummerIndividual_higherUnit_le_chosenLocalNorm hζ a ha v

end ArtinMatthews
