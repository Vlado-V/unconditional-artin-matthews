module

public import ArtinMatthews.GaloisAdicCompletionDegree
public import ArtinMatthews.KummerRowIndividualDegree
public import ArtinMatthews.SixthLocalHenselRay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual completion of an individual sixth-radical field has degree
dividing six. Combining this comparison with genuine Hensel lifting places
the explicit ray higher units in its actual local norm group. -/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ArtinMatthews

variable {F : Type*} [Field F] [NumberField F] [Algebra F ℂ]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (a : F) (ha : a ≠ 0)

include hζ ha

theorem sixthKummerIndividualCompletion_finrank_dvd_six
    (v : HeightOneSpectrum (𝓞 F))
    (W : {W : HeightOneSpectrum (𝓞 (sixthKummerRowField {a})) //
      finitePlaceBelow (K := F) W = v}) :
    let : Algebra (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
      (finitePlaceAdicCompletionMap F (sixthKummerRowField {a}) v W).toAlgebra
    Module.finrank (v.adicCompletion F)
      (W.1.adicCompletion (sixthKummerRowField {a})) ∣ 6 := by
  let : Algebra (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
    (finitePlaceAdicCompletionMap F (sixthKummerRowField {a}) v W).toAlgebra
  exact (galois_adicCompletion_finrank_dvd (K := F) (L := sixthKummerRowField {a}) v W).trans
    (sixthKummerIndividualField_finrank_dvd_six hζ a ha)

theorem sixthKummerIndividualCompletion_higherUnit_le_norm
    (v : HeightOneSpectrum (𝓞 F))
    (W : {W : HeightOneSpectrum (𝓞 (sixthKummerRowField {a})) //
      finitePlaceBelow (K := F) W = v}) :
    let : Algebra (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
      (finitePlaceAdicCompletionMap F (sixthKummerRowField {a}) v W).toAlgebra
    RayClass.localHigherUnitGroup v (sixthLocalHenselDepth v) ≤
      (Units.map (Algebra.norm (v.adicCompletion F) :
        W.1.adicCompletion (sixthKummerRowField {a}) →* v.adicCompletion F)).range := by
  let : Algebra (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
    (finitePlaceAdicCompletionMap F (sixthKummerRowField {a}) v W).toAlgebra
  let : Module.Finite (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
    finitePlaceAdicCompletionMap_moduleFinite F (sixthKummerRowField {a}) v W
  exact sixthLocal_higherUnit_le_norm v (W.1.adicCompletion (sixthKummerRowField {a}))
    (sixthKummerIndividualCompletion_finrank_dvd_six hζ a ha v W)

theorem sixthKummerIndividualCompletion_principalUnit_le_norm
    (v : HeightOneSpectrum (𝓞 F))
    (W : {W : HeightOneSpectrum (𝓞 (sixthKummerRowField {a})) //
      finitePlaceBelow (K := F) W = v}) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) :
    let : Algebra (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
      (finitePlaceAdicCompletionMap F (sixthKummerRowField {a}) v W).toAlgebra
    RayClass.localHigherUnitGroup v 1 ≤
      (Units.map (Algebra.norm (v.adicCompletion F) :
        W.1.adicCompletion (sixthKummerRowField {a}) →* v.adicCompletion F)).range := by
  let : Algebra (v.adicCompletion F) (W.1.adicCompletion (sixthKummerRowField {a})) :=
    (finitePlaceAdicCompletionMap F (sixthKummerRowField {a}) v W).toAlgebra
  simpa only [sixthLocalHenselDepth_eq_one v h6] using
    sixthKummerIndividualCompletion_higherUnit_le_norm hζ a ha v W

end ArtinMatthews
