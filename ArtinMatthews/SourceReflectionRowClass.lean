module

public import ArtinMatthews.SourceReflectionSeries
public import ArtinMatthews.SourceFrequencyOrbitSeparation
public import ArtinMatthews.SourceSixthUnitResidue


set_option backward.privateInPublic true
@[expose] public section

/-! The original coefficient depends on a row through its actual
exterior ideal and its actual S-unit sixth-power class. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "R" => sourceRing F S₀
local notation "Classes" => ExteriorUnitSixthClasses S

def sourceReflectionRowClass (m : SourceNonzeroFrequency F S₀) : Classes :=
  sourceExteriorUnitSixthClass S (sourceFrequencyUnitPart F S₀ hζ m.val m.property)

def sourceReflectionCanonicalRow (e : E) (u : Classes) : R :=
  sourceExteriorUnitToSourceRing F S₀ (sourceExteriorUnitSixthRepresentative S u) *
    sourcePrimeExponentGenerator F hζ S₀ e

theorem sourceReflectionCanonicalRow_ne_zero (e : E) (u : Classes) :
    sourceReflectionCanonicalRow F S₀ hζ e u ≠ 0 :=
  mul_ne_zero (sourceExteriorUnitToSourceRing_ne_zero F S₀ _)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ _)

theorem sourceReflectionRow_eq_canonical_mul_sixth (m : SourceNonzeroFrequency F S₀) :
    ∃ v : Rˣ, m.val =
      sourceReflectionCanonicalRow F S₀ hζ (sourceElementExponents F S₀ m.val m.property)
        (sourceReflectionRowClass F S₀ hζ m) * (v : R) ^ 6 := by
  let r := sourceFrequencyUnitPart F S₀ hζ m.val m.property
  let u := sourceReflectionRowClass F S₀ hζ m
  let t := sourceExteriorUnitSixthRepresentative S u
  let g := t⁻¹ * r
  have hq : sourceExteriorUnitSixthClass S g = 1 := by
    change sourceExteriorUnitSixthClass S (t⁻¹ * r) = 1
    rw [map_mul, map_inv]
    change (sourceExteriorUnitSixthClass S (sourceExteriorUnitSixthRepresentative S u))⁻¹ *
      sourceExteriorUnitSixthClass S r = 1
    rw [sourceExteriorUnitSixthRepresentative_class]
    exact inv_mul_cancel u
  have hg := (sourceExteriorUnitSixthClass_eq_one_iff S g).mp hq
  obtain ⟨v, hv⟩ := sourceExteriorUnitSixthPower_exists_root S ⟨g, hg⟩
  have hr : r = t * v ^ 6 := by
    change g = v ^ 6 at hv
    rw [← hv]
    exact (mul_inv_cancel_left t r).symm
  refine ⟨sourceExteriorUnitToSourceUnits F S₀ v, ?_⟩
  let e := sourceElementExponents F S₀ m.val m.property
  calc
    m.val = sourceExteriorUnitToSourceRing F S₀ r * sourcePrimeExponentGenerator F hζ S₀ e :=
      (sourceFrequencyUnitPart_factor F S₀ hζ m.val m.property).symm
    _ = _ := by
      change sourceExteriorUnitToSourceRing F S₀ r * sourcePrimeExponentGenerator F hζ S₀ e =
        sourceReflectionCanonicalRow F S₀ hζ e u * _
      rw [hr, map_mul, map_pow, sourceReflectionCanonicalRow, sourceExteriorUnitToSourceUnits_val]
      ac_rfl

variable [IsTotallyComplex F]
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

theorem sourceReflectionCoefficientRow_mul_sixth
    (hBad : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (m : R) (u : Rˣ) (Z : ℝ) :
    reflectionCoefficientRow F hζ S₀ hBad η (m * (u : R) ^ 6) Z =
      reflectionCoefficientRow F hζ S₀ hBad η m Z := by
  unfold reflectionCoefficientRow
  apply tsum_congr
  intro c
  apply tsum_congr
  intro n
  simp only [reflectionCoefficientTerm, reflectionExponentResidueValue_mul_sixth F S₀ hζ]

theorem sourceReflectionCoefficientRow_eq_canonical
    (hBad : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) (m : SourceNonzeroFrequency F S₀) (Z : ℝ) :
    reflectionCoefficientRow F hζ S₀ hBad η m.val Z =
      reflectionCoefficientRow F hζ S₀ hBad η
        (sourceReflectionCanonicalRow F S₀ hζ (sourceElementExponents F S₀ m.val m.property)
          (sourceReflectionRowClass F S₀ hζ m)) Z := by
  obtain ⟨v, hv⟩ := sourceReflectionRow_eq_canonical_mul_sixth F S₀ hζ m
  calc
    _ = reflectionCoefficientRow F hζ S₀ hBad η
        (sourceReflectionCanonicalRow F S₀ hζ (sourceElementExponents F S₀ m.val m.property)
          (sourceReflectionRowClass F S₀ hζ m) * (v : R) ^ 6) Z :=
      congrArg (fun x : R => reflectionCoefficientRow F hζ S₀ hBad η x Z) hv
    _ = _ := sourceReflectionCoefficientRow_mul_sixth F S₀ hζ η hBad _ v Z

variable {U : Type} [Fintype U]

/-- The source's reflected expansion on literal canonical ideal and unit
rows. Sixth-power invariance derives its extension to every nonzero row. -/
def SourceReflectionLiteralExpansion
    (hBad : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (A : Classes → SourceReflectionExpansionData F S₀ U) : Prop :=
  ∀ Z : ℝ, 0 < Z → ∀ (e : E) (u : Classes),
    reflectionCoefficientRow F hζ S₀ hBad η (sourceReflectionCanonicalRow F S₀ hζ e u) Z =
      sourceReflectionSelectedRow F S₀ hζ (A u) Z
        (sourceReflectionPowerfulPart e) (sourceReflectionSimplePart e) (fun _ => True)

theorem sourceReflectionLiteralExpansion_apply
    (hBad : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) {Z : ℝ} (hZ : 0 < Z)
    (m : SourceNonzeroFrequency F S₀) :
    reflectionCoefficientRow F hζ S₀ hBad η m.val Z =
      sourceReflectionSelectedRow F S₀ hζ (A (sourceReflectionRowClass F S₀ hζ m)) Z
        (sourceReflectionPowerfulPart (sourceElementExponents F S₀ m.val m.property))
        (sourceReflectionSimplePart (sourceElementExponents F S₀ m.val m.property)) (fun _ => True) :=
  (sourceReflectionCoefficientRow_eq_canonical F S₀ hζ η hBad m Z).trans (hA Z hZ _ _)

end
end ArtinMatthews.SourceEulerAssembly
