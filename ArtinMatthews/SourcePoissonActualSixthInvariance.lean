module

public import ArtinMatthews.SourceFiniteUnitFourier
public import ArtinMatthews.SourcePoissonActualFiniteFourier
public import ArtinMatthews.SourceSixthUnitResidue
public import ArtinMatthews.SourceFrequencyUnitTransversal


set_option backward.privateInPublic true
@[expose] public section

/-! The literal residue, Gauss and finite Fourier weights descend through
the actual sixth-power subgroup of the source units. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open VaryingKummerAnalytic SIntegerFourier QuadraticWeil
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => sourceHilbertSeed F S₀
local notation "R" => sourceRing F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀

theorem sourcePoissonQuotientResidue_mul_sixth (e : SourcePrimeExponents F S₀)
    (u : Rˣ) (q : R ⧸ Ideal.span {a e}) :
    sourcePoissonQuotientResidue F S₀ hζ e (sourceQuotientMulUnit _ (u ^ 6) q) =
      sourcePoissonQuotientResidue F S₀ hζ e q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  erw [sourceQuotientMulUnit_mk, sourcePoissonQuotientResidue_mk F S₀ hζ e,
    sourcePoissonQuotientResidue_mk F S₀ hζ e x, Units.val_pow_eq_pow_val]
  exact reflectionExponentResidueValue_mul_sixth F S₀ hζ e x u

theorem sourcePoissonOriginalGauss_mul_sixth (e : SourcePrimeExponents F S₀) (u : Rˣ) (m : R) :
    sourcePoissonOriginalGauss F S₀ hζ e (m * (u : R) ^ 6) =
      sourcePoissonOriginalGauss F S₀ hζ e m := by
  unfold sourcePoissonOriginalGauss
  erw [← Units.val_pow_eq_pow_val u 6]
  exact
    sourceResidueGauss_mul_unit T (a e) (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e)
      (sourcePoissonQuotientResidue F S₀ hζ e) (u ^ 6)
      (sourcePoissonQuotientResidue_mul_sixth F S₀ hζ e u) m

theorem sourcePoissonNormalizedQuotientWeight_mul_sixth (s A : SourcePrimeExponents F S₀)
    (u : Rˣ) (q : R ⧸ Ideal.span {a s * a A}) :
    sourcePoissonNormalizedQuotientWeight F S₀ hζ s A (sourceQuotientMulUnit _ (u ^ 6) q) =
      sourcePoissonNormalizedQuotientWeight F S₀ hζ s A q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  erw [sourceQuotientMulUnit_mk, sourcePoissonNormalizedQuotientWeight_mk F S₀ hζ s A,
    sourcePoissonNormalizedQuotientWeight_mk F S₀ hζ s A x, Units.val_pow_eq_pow_val, ← neg_mul,
    sourcePoissonOriginalGauss_mul_sixth F S₀ hζ s, reflectionExponentResidueValue_mul_sixth F S₀ hζ A]

theorem sourceExponentFiniteF_mul_sixth
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (s A : SourcePrimeExponents F S₀) (m : R) (u : Rˣ) :
    sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A (m * (u : R) ^ 6) =
      sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A m := by
  have h := sourceFiniteF_mul_unit_of_quotient_invariance T (a s) (a A)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s) (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A)
    (sourcePoissonProductPhase_primitive F S₀ hζ hBad s A)
    (sourcePoissonQuotientResidue F S₀ hζ s) (sourcePoissonQuotientResidue F S₀ hζ A) (u ^ 6)
    (sourcePoissonQuotientResidue_mul_sixth F S₀ hζ s u)
    (sourcePoissonQuotientResidue_mul_sixth F S₀ hζ A u) m
  have hf (e : SourcePrimeExponents F S₀) :
      (fun x : R => sourcePoissonQuotientResidue F S₀ hζ e
        (Ideal.Quotient.mk (Ideal.span {a e} : Ideal R) x)) =
      reflectionExponentResidueValue F hζ S₀ e :=
    funext (sourcePoissonQuotientResidue_mk F S₀ hζ e)
  erw [hf s, hf A, Units.val_pow_eq_pow_val u 6] at h
  exact h

theorem sourceExponentFiniteF_mul_orbitSixth
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (s A : SourcePrimeExponents F S₀) (m : R)
    (v : SourceExteriorUnitSixthPowers (sourceHilbertSet F S₀)) :
    sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A
      (m * sourceExteriorUnitToSourceRing F S₀ v.val) =
      sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A m := by
  obtain ⟨u, hu⟩ := sourceExteriorUnitSixthPower_exists_root (sourceHilbertSet F S₀) v
  rw [hu, map_pow]
  exact sourceExponentFiniteF_mul_sixth F S₀ hζ hBad s A m (sourceExteriorUnitToSourceUnits F S₀ u)

end
end ArtinMatthews.SourceEulerAssembly
