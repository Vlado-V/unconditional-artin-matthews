module

public import ArtinMatthews.SourceExteriorDirichletIdentification
public import ArtinMatthews.SourceGlobalCorrectionAnalytic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal source series and the exact angular Mellin
amplitude after the two exterior Dedekind factors are extracted. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
local notation "S" => sourceHilbertSet F S₀

def sourcePrincipalEulerAmplitude (q : ProbeCoordinates) : ℂ :=
  sourceGlobalCorrection F hζ S₀ η 1 one_ne_zero q * (principalAngularExteriorL η S q.1)⁻¹

theorem sourcePrincipalEulerAmplitude_specialize (s : ℂ) :
    sourcePrincipalEulerAmplitude F hζ S₀ η (s, 1, 1 / 6) =
      principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹ := by
  unfold sourcePrincipalEulerAmplitude
  rw [sourceGlobalCorrection_one_specialize]

variable [IsTotallyComplex F]

theorem sourceGlobalCalF_principal
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hcut : probePrimeCutoff F ⊆ S) (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceGlobalCalF F hζ S₀ hS η 1 ξ w z =
      principalExteriorZeta S (6 * z) * principalExteriorZeta S w *
        sourcePrincipalEulerAmplitude F hζ S₀ η (ξ, w, z) := by
  have ha : sourcePrimeRowCharacter F hζ S₀ 1 one_ne_zero = fun _ => 1 :=
    funext (sourcePrimeRowCharacter_one F hζ S₀)
  have hb : sourcePrimeRowTwist F hζ S₀ 1 one_ne_zero η = fun P => η.allCoefficient P.val.asIdeal := by
    funext P
    rw [sourcePrimeRowTwist, sourcePrimeRowCharacter_one F hζ S₀ P, star_one, mul_one]
  have hz₁ : 1 < (6 * z).re := by
    have he : ((6 : ℂ) * z).re = 6 * z.re := by norm_num [Complex.mul_re]
    rw [he]
    linarith
  rw [sourceGlobalCalF_eq_normalized F hζ S₀ hS η 1 one_ne_zero ξ w z hcut hξ hw hz, ha, hb,
    sourceExteriorValueEuler_eq_exteriorZeta F S₀ (6 * z) hz₁,
    sourceExteriorValueEuler_eq_exteriorZeta F S₀ w (by linarith),
    sourceExteriorValueEuler_eq_angularL F S₀ η ξ (by linarith)]
  unfold sourcePrincipalEulerAmplitude
  rw [div_eq_mul_inv]
  ac_rfl

end
end ArtinMatthews.SourceEulerAssembly
