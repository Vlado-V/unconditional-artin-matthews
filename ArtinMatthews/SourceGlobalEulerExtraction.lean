module

public import ArtinMatthews.SourceGlobalCorrection
public import ArtinMatthews.SourceExteriorValueEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The exact global source Euler extraction on its initial domain.
All products have proved convergence and the denominator product is
nonzero there. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (u : sourceRing F S₀) (hu : u ≠ 0)
variable (ξ w z : ℂ)

theorem sourceGlobalCalF_eq_normalized (hcut : probePrimeCutoff F ⊆ sourceHilbertSet F S₀)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceGlobalCalF F hζ S₀ hS η u ξ w z =
      sourceExteriorValueEuler F S₀ (fun _ => 1) (6 * z) *
      sourceExteriorValueEuler F S₀ (sourcePrimeRowCharacter F hζ S₀ u hu) w /
      sourceExteriorValueEuler F S₀ (sourcePrimeRowTwist F hζ S₀ u hu η) ξ *
      sourceGlobalCorrection F hζ S₀ η u hu (ξ, w, z) := by
  let a := sourcePrimeRowCharacter F hζ S₀ u hu
  let b := sourcePrimeRowTwist F hζ S₀ u hu η
  have hξ₁ : 1 < ξ.re := by linarith
  have hw₁ : 1 < w.re := by linarith
  have hz₁ : 1 < (6 * z).re := by
    have he : ((6 : ℂ) * z).re = 6 * z.re := by norm_num [Complex.mul_re]
    rw [he]
    linarith
  have hV := sourceExteriorValueEuler_hasProd F S₀ (fun _ => 1) (fun _ => by simp) (6 * z) hz₁
  have hW := sourceExteriorValueEuler_hasProd F S₀ a
    (sourcePrimeRowCharacter_norm_le_one F hζ S₀ u hu) w hw₁
  have hD := sourceExteriorValueEuler_hasProd F S₀ b
    (sourcePrimeRowTwist_norm_le_one F hζ S₀ u hu η) ξ hξ₁
  have hD0 := sourceExteriorValueEuler_ne_zero F S₀ b
    (sourcePrimeRowTwist_norm_le_one F hζ S₀ u hu η) ξ hξ₁
  have hH := sourceGlobalCorrection_hasProd F hζ S₀ η u hu hcut (ξ, w, z)
    (sourceInitialCoordinates_region ξ w z hξ hw hz)
  have hProd := ((hV.mul hW).mul (hD.inv₀ hD0)).mul hH
  have h : HasProd (sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z)
      (sourceExteriorValueEuler F S₀ (fun _ => 1) (6 * z) *
      sourceExteriorValueEuler F S₀ a w /
      sourceExteriorValueEuler F S₀ b ξ *
      sourceGlobalCorrection F hζ S₀ η u hu (ξ, w, z)) := by
    rw [div_eq_mul_inv]
    apply hProd.congr_fun
    intro P
    simpa only [sourcePrimeEulerRatio, probeLocalV, probeLocalW, probeLocalD,
      Complex.ofReal_natCast, one_mul, inv_inv, a, b] using
      sourceLocalEulerFactor_normalized F hζ S₀ hS η u hu P ξ w z hξ hw hz
  exact (sourceGlobalCalF_hasProd F hζ S₀ hS η u hu ξ w z hξ hw hz).unique h

end
end ArtinMatthews.SourceEulerAssembly
