module

public import ArtinMatthews.SourcePoissonOriginalUnitChange


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SourcePhysical
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourcePoissonReflectionCoefficientRow_mul_sixth
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (u : Rˣ) (m : R) (Z : ℝ) :
    reflectionCoefficientRow F hζ S₀ hBad η (m * (u : R) ^ 6) Z =
      reflectionCoefficientRow F hζ S₀ hBad η m Z := by
  unfold reflectionCoefficientRow
  apply tsum_congr
  intro c
  apply tsum_congr
  intro n
  unfold reflectionCoefficientTerm
  dsimp only
  rw [reflectionExponentResidueValue_mul_sixth F S₀ hζ]

/-- Change the norm-one representative and reindex the original S-integer
sum by multiplication by the corresponding genuine source-ring unit. -/
theorem sourcePoissonOriginalDensity_mul_sixth_of_gauss
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (u : SUnitGroup (K := F) S) (t : SNormOne F S) (X Y Z : ℝ)
    (hGauss : ∀ (s : SourcePrimeExponents F S₀) (m : R),
      sourcePoissonOriginalGauss F S₀ hζ s (m * (sourcePoissonPrimalUnit F S₀ u : R) ^ 6) =
        sourcePoissonOriginalGauss F S₀ hζ s m) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z (t * sNormOneSixthMap F S u) =
      sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t := by
  let ε := sourcePoissonPrimalUnit F S₀ u
  let t' : SNormOne F S := t * sNormOneSixthMap F S u
  let e : R ≃ R := (ε ^ 6).mulRight
  have he (m : R) : e m = m * (ε : R) ^ 6 := by
    change m * ((ε ^ 6 : Rˣ) : R) = m * (ε : R) ^ 6
    rw [Units.val_pow_eq_pow_val]
  let g (t₀ : SNormOne F S) (s : SourcePrimeExponents F S₀) (m : R) : ℂ :=
    (sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
    sourcePoissonOriginalTest F S₀ hζ t₀ ((q s : ℝ) * X) m *
    reflectionCoefficientRow F hζ S₀ hBad η m Z
  have hPoint (s : SourcePrimeExponents F S₀) (m : R) : g t' s (e m) = g t s m := by
    rw [he]
    dsimp only [g, t', ε]
    have hG := hGauss s (-m)
    rw [neg_mul] at hG
    rw [hG, sourcePoissonOriginalTest_mul_sixth F S₀ hζ u t ((q s : ℝ) * X) m,
      sourcePoissonReflectionCoefficientRow_mul_sixth F S₀ hζ η hBad]
  have hReindex (s : SourcePrimeExponents F S₀) :
      (∑' m : R, g t' s m) = ∑' m : R, g t s m :=
    (e.tsum_eq (g t' s)).symm.trans (tsum_congr (hPoint s))
  let H (s : SourcePrimeExponents F S₀) (b : ℂ) : ℂ :=
    sourceProbeW1Complex ((q s : ℝ) / Y) * ((Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹ * b)
  have hOuter : (∑' s, H s (∑' m, g t' s m)) = ∑' s, H s (∑' m, g t s m) :=
    tsum_congr fun s => congrArg (H s) (hReindex s)
  exact congrArg (fun z : ℂ => (Y : ℂ)⁻¹ * z) hOuter

end
end ArtinMatthews.SourceEulerAssembly
